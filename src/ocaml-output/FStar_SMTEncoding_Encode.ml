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
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_All.pipe_right (FStar_Util.prefix vars)
                        FStar_Pervasives_Native.fst
                       in
                    let axiom_name = Prims.op_Hat "primitive_tot_fun_" x1  in
                    let tot_fun_axiom_for_x =
                      let uu____389 =
                        let uu____397 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1  in
                        (uu____397, FStar_Pervasives_Native.None, axiom_name)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____389  in
                    let uu____400 =
                      FStar_List.fold_left
                        (fun uu____454  ->
                           fun var  ->
                             match uu____454 with
                             | (axioms,app,vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var]
                                    in
                                 let vars2 = FStar_List.append vars1 [var]
                                    in
                                 let axiom_name1 =
                                   let uu____581 =
                                     let uu____583 =
                                       let uu____585 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length
                                          in
                                       Prims.string_of_int uu____585  in
                                     Prims.op_Hat "." uu____583  in
                                   Prims.op_Hat axiom_name uu____581  in
                                 let uu____607 =
                                   let uu____610 =
                                     let uu____613 =
                                       let uu____614 =
                                         let uu____622 =
                                           let uu____623 =
                                             let uu____634 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1
                                                in
                                             ([[app1]], vars2, uu____634)  in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____623
                                            in
                                         (uu____622,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1)
                                          in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____614
                                        in
                                     [uu____613]  in
                                   FStar_List.append axioms uu____610  in
                                 (uu____607, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one
                       in
                    match uu____400 with
                    | (axioms,uu____680,uu____681) -> axioms  in
                  let uu____706 =
                    let uu____709 =
                      let uu____712 =
                        let uu____715 =
                          let uu____718 =
                            let uu____719 =
                              let uu____727 =
                                let uu____728 =
                                  let uu____739 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, uu____739)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____728
                                 in
                              (uu____727, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____719  in
                          [uu____718]  in
                        xtok_decl :: uu____715  in
                      xname_decl :: uu____712  in
                    let uu____751 =
                      let uu____754 =
                        let uu____757 =
                          let uu____758 =
                            let uu____766 =
                              let uu____767 =
                                let uu____778 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp)
                                   in
                                ([[xtok_app]], vars, uu____778)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____767
                               in
                            (uu____766,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____758  in
                        [uu____757]  in
                      FStar_List.append tot_fun_axioms uu____754  in
                    FStar_List.append uu____709 uu____751  in
                  (xtok1, (FStar_List.length vars), uu____706)  in
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
                  let uu____948 =
                    let uu____969 =
                      let uu____988 =
                        let uu____989 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____989
                         in
                      quant axy uu____988  in
                    (FStar_Parser_Const.op_Eq, uu____969)  in
                  let uu____1006 =
                    let uu____1029 =
                      let uu____1050 =
                        let uu____1069 =
                          let uu____1070 =
                            let uu____1071 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____1071  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1070
                           in
                        quant axy uu____1069  in
                      (FStar_Parser_Const.op_notEq, uu____1050)  in
                    let uu____1088 =
                      let uu____1111 =
                        let uu____1132 =
                          let uu____1151 =
                            let uu____1152 =
                              let uu____1153 =
                                let uu____1158 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____1159 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____1158, uu____1159)  in
                              FStar_SMTEncoding_Util.mkAnd uu____1153  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1152
                             in
                          quant xy uu____1151  in
                        (FStar_Parser_Const.op_And, uu____1132)  in
                      let uu____1176 =
                        let uu____1199 =
                          let uu____1220 =
                            let uu____1239 =
                              let uu____1240 =
                                let uu____1241 =
                                  let uu____1246 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____1247 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____1246, uu____1247)  in
                                FStar_SMTEncoding_Util.mkOr uu____1241  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1240
                               in
                            quant xy uu____1239  in
                          (FStar_Parser_Const.op_Or, uu____1220)  in
                        let uu____1264 =
                          let uu____1287 =
                            let uu____1308 =
                              let uu____1327 =
                                let uu____1328 =
                                  let uu____1329 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____1329  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1328
                                 in
                              quant qx uu____1327  in
                            (FStar_Parser_Const.op_Negation, uu____1308)  in
                          let uu____1346 =
                            let uu____1369 =
                              let uu____1390 =
                                let uu____1409 =
                                  let uu____1410 =
                                    let uu____1411 =
                                      let uu____1416 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1417 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1416, uu____1417)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1411
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1410
                                   in
                                quant xy uu____1409  in
                              (FStar_Parser_Const.op_LT, uu____1390)  in
                            let uu____1434 =
                              let uu____1457 =
                                let uu____1478 =
                                  let uu____1497 =
                                    let uu____1498 =
                                      let uu____1499 =
                                        let uu____1504 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1505 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1504, uu____1505)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1499
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1498
                                     in
                                  quant xy uu____1497  in
                                (FStar_Parser_Const.op_LTE, uu____1478)  in
                              let uu____1522 =
                                let uu____1545 =
                                  let uu____1566 =
                                    let uu____1585 =
                                      let uu____1586 =
                                        let uu____1587 =
                                          let uu____1592 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1593 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1592, uu____1593)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1587
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1586
                                       in
                                    quant xy uu____1585  in
                                  (FStar_Parser_Const.op_GT, uu____1566)  in
                                let uu____1610 =
                                  let uu____1633 =
                                    let uu____1654 =
                                      let uu____1673 =
                                        let uu____1674 =
                                          let uu____1675 =
                                            let uu____1680 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1681 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1680, uu____1681)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1675
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1674
                                         in
                                      quant xy uu____1673  in
                                    (FStar_Parser_Const.op_GTE, uu____1654)
                                     in
                                  let uu____1698 =
                                    let uu____1721 =
                                      let uu____1742 =
                                        let uu____1761 =
                                          let uu____1762 =
                                            let uu____1763 =
                                              let uu____1768 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1769 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1768, uu____1769)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1763
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1762
                                           in
                                        quant xy uu____1761  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1742)
                                       in
                                    let uu____1786 =
                                      let uu____1809 =
                                        let uu____1830 =
                                          let uu____1849 =
                                            let uu____1850 =
                                              let uu____1851 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1851
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1850
                                             in
                                          quant qx uu____1849  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1830)
                                         in
                                      let uu____1868 =
                                        let uu____1891 =
                                          let uu____1912 =
                                            let uu____1931 =
                                              let uu____1932 =
                                                let uu____1933 =
                                                  let uu____1938 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1939 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1938, uu____1939)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1933
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1932
                                               in
                                            quant xy uu____1931  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1912)
                                           in
                                        let uu____1956 =
                                          let uu____1979 =
                                            let uu____2000 =
                                              let uu____2019 =
                                                let uu____2020 =
                                                  let uu____2021 =
                                                    let uu____2026 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____2027 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____2026, uu____2027)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2021
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2020
                                                 in
                                              quant xy uu____2019  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2000)
                                             in
                                          let uu____2044 =
                                            let uu____2067 =
                                              let uu____2088 =
                                                let uu____2107 =
                                                  let uu____2108 =
                                                    let uu____2109 =
                                                      let uu____2114 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____2115 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____2114,
                                                        uu____2115)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2109
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2108
                                                   in
                                                quant xy uu____2107  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2088)
                                               in
                                            let uu____2132 =
                                              let uu____2155 =
                                                let uu____2176 =
                                                  let uu____2195 =
                                                    let uu____2196 =
                                                      let uu____2197 =
                                                        let uu____2202 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____2203 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____2202,
                                                          uu____2203)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2197
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2196
                                                     in
                                                  quant xy uu____2195  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2176)
                                                 in
                                              let uu____2220 =
                                                let uu____2243 =
                                                  let uu____2264 =
                                                    let uu____2283 =
                                                      let uu____2284 =
                                                        let uu____2285 =
                                                          let uu____2290 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____2291 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____2290,
                                                            uu____2291)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2285
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2284
                                                       in
                                                    quant xy uu____2283  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2264)
                                                   in
                                                let uu____2308 =
                                                  let uu____2331 =
                                                    let uu____2352 =
                                                      let uu____2371 =
                                                        let uu____2372 =
                                                          let uu____2373 =
                                                            let uu____2378 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____2379 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____2378,
                                                              uu____2379)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2373
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2372
                                                         in
                                                      quant xy uu____2371  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2352)
                                                     in
                                                  let uu____2396 =
                                                    let uu____2419 =
                                                      let uu____2440 =
                                                        let uu____2459 =
                                                          let uu____2460 =
                                                            let uu____2461 =
                                                              let uu____2466
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2467
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2466,
                                                                uu____2467)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2461
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2460
                                                           in
                                                        quant xy uu____2459
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2440)
                                                       in
                                                    let uu____2484 =
                                                      let uu____2507 =
                                                        let uu____2528 =
                                                          let uu____2547 =
                                                            let uu____2548 =
                                                              let uu____2549
                                                                =
                                                                let uu____2554
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2555
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2554,
                                                                  uu____2555)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2549
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2548
                                                             in
                                                          quant xy uu____2547
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2528)
                                                         in
                                                      let uu____2572 =
                                                        let uu____2595 =
                                                          let uu____2616 =
                                                            let uu____2635 =
                                                              let uu____2636
                                                                =
                                                                let uu____2637
                                                                  =
                                                                  let uu____2642
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2643
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2642,
                                                                    uu____2643)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2637
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2636
                                                               in
                                                            quant xy
                                                              uu____2635
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2616)
                                                           in
                                                        let uu____2660 =
                                                          let uu____2683 =
                                                            let uu____2704 =
                                                              let uu____2723
                                                                =
                                                                let uu____2724
                                                                  =
                                                                  let uu____2725
                                                                    =
                                                                    let uu____2730
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2731
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2730,
                                                                    uu____2731)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2725
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2724
                                                                 in
                                                              quant xy
                                                                uu____2723
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2704)
                                                             in
                                                          let uu____2748 =
                                                            let uu____2771 =
                                                              let uu____2792
                                                                =
                                                                let uu____2811
                                                                  =
                                                                  let uu____2812
                                                                    =
                                                                    let uu____2813
                                                                    =
                                                                    let uu____2818
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2819
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2818,
                                                                    uu____2819)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2813
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2812
                                                                   in
                                                                quant xy
                                                                  uu____2811
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2792)
                                                               in
                                                            let uu____2836 =
                                                              let uu____2859
                                                                =
                                                                let uu____2880
                                                                  =
                                                                  let uu____2899
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    let uu____2906
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2907
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2906,
                                                                    uu____2907)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2901
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2900
                                                                     in
                                                                  quant xy
                                                                    uu____2899
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2880)
                                                                 in
                                                              let uu____2924
                                                                =
                                                                let uu____2947
                                                                  =
                                                                  let uu____2968
                                                                    =
                                                                    let uu____2987
                                                                    =
                                                                    let uu____2988
                                                                    =
                                                                    let uu____2989
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2989
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2988
                                                                     in
                                                                    quant qx
                                                                    uu____2987
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2968)
                                                                   in
                                                                [uu____2947]
                                                                 in
                                                              uu____2859 ::
                                                                uu____2924
                                                               in
                                                            uu____2771 ::
                                                              uu____2836
                                                             in
                                                          uu____2683 ::
                                                            uu____2748
                                                           in
                                                        uu____2595 ::
                                                          uu____2660
                                                         in
                                                      uu____2507 ::
                                                        uu____2572
                                                       in
                                                    uu____2419 :: uu____2484
                                                     in
                                                  uu____2331 :: uu____2396
                                                   in
                                                uu____2243 :: uu____2308  in
                                              uu____2155 :: uu____2220  in
                                            uu____2067 :: uu____2132  in
                                          uu____1979 :: uu____2044  in
                                        uu____1891 :: uu____1956  in
                                      uu____1809 :: uu____1868  in
                                    uu____1721 :: uu____1786  in
                                  uu____1633 :: uu____1698  in
                                uu____1545 :: uu____1610  in
                              uu____1457 :: uu____1522  in
                            uu____1369 :: uu____1434  in
                          uu____1287 :: uu____1346  in
                        uu____1199 :: uu____1264  in
                      uu____1111 :: uu____1176  in
                    uu____1029 :: uu____1088  in
                  uu____948 :: uu____1006  in
                let mk1 l v1 =
                  let uu____3528 =
                    let uu____3540 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____3630  ->
                              match uu____3630 with
                              | (l',uu____3651) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3540
                      (FStar_Option.map
                         (fun uu____3750  ->
                            match uu____3750 with
                            | (uu____3778,b) ->
                                let uu____3812 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3812 v1))
                     in
                  FStar_All.pipe_right uu____3528 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3895  ->
                          match uu____3895 with
                          | (l',uu____3916) -> FStar_Ident.lid_equals l l'))
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
          let uu____3990 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____3990 with
          | (xxsym,xx) ->
              let uu____4001 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____4001 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____4017 =
                     let uu____4025 =
                       let uu____4026 =
                         let uu____4037 =
                           let uu____4038 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____4048 =
                             let uu____4059 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____4059 :: vars  in
                           uu____4038 :: uu____4048  in
                         let uu____4085 =
                           let uu____4086 =
                             let uu____4091 =
                               let uu____4092 =
                                 let uu____4097 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____4097)  in
                               FStar_SMTEncoding_Util.mkEq uu____4092  in
                             (xx_has_type, uu____4091)  in
                           FStar_SMTEncoding_Util.mkImp uu____4086  in
                         ([[xx_has_type]], uu____4037, uu____4085)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____4026  in
                     let uu____4110 =
                       let uu____4112 =
                         let uu____4114 =
                           let uu____4116 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____4116  in
                         Prims.op_Hat module_name uu____4114  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____4112
                        in
                     (uu____4025, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____4110)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____4017)
  
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
    let uu____4172 =
      let uu____4174 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____4174  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4172  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____4196 =
      let uu____4197 =
        let uu____4205 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____4205, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4197  in
    let uu____4210 =
      let uu____4213 =
        let uu____4214 =
          let uu____4222 =
            let uu____4223 =
              let uu____4234 =
                let uu____4235 =
                  let uu____4240 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____4240)  in
                FStar_SMTEncoding_Util.mkImp uu____4235  in
              ([[typing_pred]], [xx], uu____4234)  in
            let uu____4265 =
              let uu____4280 = FStar_TypeChecker_Env.get_range env  in
              let uu____4281 = mkForall_fuel1 env  in uu____4281 uu____4280
               in
            uu____4265 uu____4223  in
          (uu____4222, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4214  in
      [uu____4213]  in
    uu____4196 :: uu____4210  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4328 =
      let uu____4329 =
        let uu____4337 =
          let uu____4338 = FStar_TypeChecker_Env.get_range env  in
          let uu____4339 =
            let uu____4350 =
              let uu____4355 =
                let uu____4358 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____4358]  in
              [uu____4355]  in
            let uu____4363 =
              let uu____4364 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4364 tt  in
            (uu____4350, [bb], uu____4363)  in
          FStar_SMTEncoding_Term.mkForall uu____4338 uu____4339  in
        (uu____4337, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4329  in
    let uu____4389 =
      let uu____4392 =
        let uu____4393 =
          let uu____4401 =
            let uu____4402 =
              let uu____4413 =
                let uu____4414 =
                  let uu____4419 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4419)  in
                FStar_SMTEncoding_Util.mkImp uu____4414  in
              ([[typing_pred]], [xx], uu____4413)  in
            let uu____4446 =
              let uu____4461 = FStar_TypeChecker_Env.get_range env  in
              let uu____4462 = mkForall_fuel1 env  in uu____4462 uu____4461
               in
            uu____4446 uu____4402  in
          (uu____4401, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4393  in
      [uu____4392]  in
    uu____4328 :: uu____4389  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4505 =
        let uu____4506 =
          let uu____4512 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4512, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4506  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4505  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4526 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4526  in
    let uu____4531 =
      let uu____4532 =
        let uu____4540 =
          let uu____4541 = FStar_TypeChecker_Env.get_range env  in
          let uu____4542 =
            let uu____4553 =
              let uu____4558 =
                let uu____4561 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4561]  in
              [uu____4558]  in
            let uu____4566 =
              let uu____4567 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4567 tt  in
            (uu____4553, [bb], uu____4566)  in
          FStar_SMTEncoding_Term.mkForall uu____4541 uu____4542  in
        (uu____4540, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4532  in
    let uu____4592 =
      let uu____4595 =
        let uu____4596 =
          let uu____4604 =
            let uu____4605 =
              let uu____4616 =
                let uu____4617 =
                  let uu____4622 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4622)  in
                FStar_SMTEncoding_Util.mkImp uu____4617  in
              ([[typing_pred]], [xx], uu____4616)  in
            let uu____4649 =
              let uu____4664 = FStar_TypeChecker_Env.get_range env  in
              let uu____4665 = mkForall_fuel1 env  in uu____4665 uu____4664
               in
            uu____4649 uu____4605  in
          (uu____4604, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4596  in
      let uu____4687 =
        let uu____4690 =
          let uu____4691 =
            let uu____4699 =
              let uu____4700 =
                let uu____4711 =
                  let uu____4712 =
                    let uu____4717 =
                      let uu____4718 =
                        let uu____4721 =
                          let uu____4724 =
                            let uu____4727 =
                              let uu____4728 =
                                let uu____4733 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4734 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____4733, uu____4734)  in
                              FStar_SMTEncoding_Util.mkGT uu____4728  in
                            let uu____4736 =
                              let uu____4739 =
                                let uu____4740 =
                                  let uu____4745 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4746 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____4745, uu____4746)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4740  in
                              let uu____4748 =
                                let uu____4751 =
                                  let uu____4752 =
                                    let uu____4757 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4758 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4757, uu____4758)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4752  in
                                [uu____4751]  in
                              uu____4739 :: uu____4748  in
                            uu____4727 :: uu____4736  in
                          typing_pred_y :: uu____4724  in
                        typing_pred :: uu____4721  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4718  in
                    (uu____4717, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4712  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4711)
                 in
              let uu____4791 =
                let uu____4806 = FStar_TypeChecker_Env.get_range env  in
                let uu____4807 = mkForall_fuel1 env  in uu____4807 uu____4806
                 in
              uu____4791 uu____4700  in
            (uu____4699,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4691  in
        [uu____4690]  in
      uu____4595 :: uu____4687  in
    uu____4531 :: uu____4592  in
  let mk_real env nm tt =
    let lex_t1 =
      let uu____4850 =
        let uu____4851 =
          let uu____4857 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4857, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4851  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4850  in
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
      let uu____4873 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4873  in
    let uu____4878 =
      let uu____4879 =
        let uu____4887 =
          let uu____4888 = FStar_TypeChecker_Env.get_range env  in
          let uu____4889 =
            let uu____4900 =
              let uu____4905 =
                let uu____4908 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4908]  in
              [uu____4905]  in
            let uu____4913 =
              let uu____4914 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4914 tt  in
            (uu____4900, [bb], uu____4913)  in
          FStar_SMTEncoding_Term.mkForall uu____4888 uu____4889  in
        (uu____4887, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4879  in
    let uu____4939 =
      let uu____4942 =
        let uu____4943 =
          let uu____4951 =
            let uu____4952 =
              let uu____4963 =
                let uu____4964 =
                  let uu____4969 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____4969)  in
                FStar_SMTEncoding_Util.mkImp uu____4964  in
              ([[typing_pred]], [xx], uu____4963)  in
            let uu____4996 =
              let uu____5011 = FStar_TypeChecker_Env.get_range env  in
              let uu____5012 = mkForall_fuel1 env  in uu____5012 uu____5011
               in
            uu____4996 uu____4952  in
          (uu____4951, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4943  in
      let uu____5034 =
        let uu____5037 =
          let uu____5038 =
            let uu____5046 =
              let uu____5047 =
                let uu____5058 =
                  let uu____5059 =
                    let uu____5064 =
                      let uu____5065 =
                        let uu____5068 =
                          let uu____5071 =
                            let uu____5074 =
                              let uu____5075 =
                                let uu____5080 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____5081 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____5080, uu____5081)  in
                              FStar_SMTEncoding_Util.mkGT uu____5075  in
                            let uu____5083 =
                              let uu____5086 =
                                let uu____5087 =
                                  let uu____5092 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____5093 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____5092, uu____5093)  in
                                FStar_SMTEncoding_Util.mkGTE uu____5087  in
                              let uu____5095 =
                                let uu____5098 =
                                  let uu____5099 =
                                    let uu____5104 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____5105 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____5104, uu____5105)  in
                                  FStar_SMTEncoding_Util.mkLT uu____5099  in
                                [uu____5098]  in
                              uu____5086 :: uu____5095  in
                            uu____5074 :: uu____5083  in
                          typing_pred_y :: uu____5071  in
                        typing_pred :: uu____5068  in
                      FStar_SMTEncoding_Util.mk_and_l uu____5065  in
                    (uu____5064, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____5059  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____5058)
                 in
              let uu____5138 =
                let uu____5153 = FStar_TypeChecker_Env.get_range env  in
                let uu____5154 = mkForall_fuel1 env  in uu____5154 uu____5153
                 in
              uu____5138 uu____5047  in
            (uu____5046,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____5038  in
        [uu____5037]  in
      uu____4942 :: uu____5034  in
    uu____4878 :: uu____4939  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____5201 =
      let uu____5202 =
        let uu____5210 =
          let uu____5211 = FStar_TypeChecker_Env.get_range env  in
          let uu____5212 =
            let uu____5223 =
              let uu____5228 =
                let uu____5231 = FStar_SMTEncoding_Term.boxString b  in
                [uu____5231]  in
              [uu____5228]  in
            let uu____5236 =
              let uu____5237 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____5237 tt  in
            (uu____5223, [bb], uu____5236)  in
          FStar_SMTEncoding_Term.mkForall uu____5211 uu____5212  in
        (uu____5210, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5202  in
    let uu____5262 =
      let uu____5265 =
        let uu____5266 =
          let uu____5274 =
            let uu____5275 =
              let uu____5286 =
                let uu____5287 =
                  let uu____5292 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____5292)  in
                FStar_SMTEncoding_Util.mkImp uu____5287  in
              ([[typing_pred]], [xx], uu____5286)  in
            let uu____5319 =
              let uu____5334 = FStar_TypeChecker_Env.get_range env  in
              let uu____5335 = mkForall_fuel1 env  in uu____5335 uu____5334
               in
            uu____5319 uu____5275  in
          (uu____5274, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____5266  in
      [uu____5265]  in
    uu____5201 :: uu____5262  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____5382 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____5382]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5412 =
      let uu____5413 =
        let uu____5421 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5421, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5413  in
    [uu____5412]  in
  let mk_and_interp env conj uu____5444 =
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
    let uu____5473 =
      let uu____5474 =
        let uu____5482 =
          let uu____5483 = FStar_TypeChecker_Env.get_range env  in
          let uu____5484 =
            let uu____5495 =
              let uu____5496 =
                let uu____5501 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5501, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5496  in
            ([[l_and_a_b]], [aa; bb], uu____5495)  in
          FStar_SMTEncoding_Term.mkForall uu____5483 uu____5484  in
        (uu____5482, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5474  in
    [uu____5473]  in
  let mk_or_interp env disj uu____5556 =
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
    let uu____5585 =
      let uu____5586 =
        let uu____5594 =
          let uu____5595 = FStar_TypeChecker_Env.get_range env  in
          let uu____5596 =
            let uu____5607 =
              let uu____5608 =
                let uu____5613 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5613, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5608  in
            ([[l_or_a_b]], [aa; bb], uu____5607)  in
          FStar_SMTEncoding_Term.mkForall uu____5595 uu____5596  in
        (uu____5594, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5586  in
    [uu____5585]  in
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
    let uu____5691 =
      let uu____5692 =
        let uu____5700 =
          let uu____5701 = FStar_TypeChecker_Env.get_range env  in
          let uu____5702 =
            let uu____5713 =
              let uu____5714 =
                let uu____5719 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5719, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5714  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5713)  in
          FStar_SMTEncoding_Term.mkForall uu____5701 uu____5702  in
        (uu____5700, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5692  in
    [uu____5691]  in
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
    let uu____5809 =
      let uu____5810 =
        let uu____5818 =
          let uu____5819 = FStar_TypeChecker_Env.get_range env  in
          let uu____5820 =
            let uu____5831 =
              let uu____5832 =
                let uu____5837 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5837, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5832  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5831)  in
          FStar_SMTEncoding_Term.mkForall uu____5819 uu____5820  in
        (uu____5818, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5810  in
    [uu____5809]  in
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
    let uu____5937 =
      let uu____5938 =
        let uu____5946 =
          let uu____5947 = FStar_TypeChecker_Env.get_range env  in
          let uu____5948 =
            let uu____5959 =
              let uu____5960 =
                let uu____5965 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____5965, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5960  in
            ([[l_imp_a_b]], [aa; bb], uu____5959)  in
          FStar_SMTEncoding_Term.mkForall uu____5947 uu____5948  in
        (uu____5946, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5938  in
    [uu____5937]  in
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
    let uu____6049 =
      let uu____6050 =
        let uu____6058 =
          let uu____6059 = FStar_TypeChecker_Env.get_range env  in
          let uu____6060 =
            let uu____6071 =
              let uu____6072 =
                let uu____6077 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____6077, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____6072  in
            ([[l_iff_a_b]], [aa; bb], uu____6071)  in
          FStar_SMTEncoding_Term.mkForall uu____6059 uu____6060  in
        (uu____6058, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6050  in
    [uu____6049]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____6148 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____6148  in
    let uu____6153 =
      let uu____6154 =
        let uu____6162 =
          let uu____6163 = FStar_TypeChecker_Env.get_range env  in
          let uu____6164 =
            let uu____6175 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____6175)  in
          FStar_SMTEncoding_Term.mkForall uu____6163 uu____6164  in
        (uu____6162, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6154  in
    [uu____6153]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____6228 =
      let uu____6229 =
        let uu____6237 =
          let uu____6238 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____6238 range_ty  in
        let uu____6239 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____6237, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____6239)
         in
      FStar_SMTEncoding_Util.mkAssume uu____6229  in
    [uu____6228]  in
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
        let uu____6285 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____6285 x1 t  in
      let uu____6287 = FStar_TypeChecker_Env.get_range env  in
      let uu____6288 =
        let uu____6299 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____6299)  in
      FStar_SMTEncoding_Term.mkForall uu____6287 uu____6288  in
    let uu____6324 =
      let uu____6325 =
        let uu____6333 =
          let uu____6334 = FStar_TypeChecker_Env.get_range env  in
          let uu____6335 =
            let uu____6346 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____6346)  in
          FStar_SMTEncoding_Term.mkForall uu____6334 uu____6335  in
        (uu____6333,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6325  in
    [uu____6324]  in
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
    let uu____6407 =
      let uu____6408 =
        let uu____6416 =
          let uu____6417 = FStar_TypeChecker_Env.get_range env  in
          let uu____6418 =
            let uu____6434 =
              let uu____6435 =
                let uu____6440 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6441 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6440, uu____6441)  in
              FStar_SMTEncoding_Util.mkAnd uu____6435  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____6434)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6417 uu____6418  in
        (uu____6416,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6408  in
    [uu____6407]  in
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
          let uu____6999 =
            FStar_Util.find_opt
              (fun uu____7037  ->
                 match uu____7037 with
                 | (l,uu____7053) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____6999 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____7096,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7157 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____7157 with
        | (form,decls) ->
            let uu____7166 =
              let uu____7169 =
                let uu____7172 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____7172]  in
              FStar_All.pipe_right uu____7169
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____7166
  
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
              let uu____7231 =
                ((let uu____7235 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____7235) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____7231
              then
                let arg_sorts =
                  let uu____7247 =
                    let uu____7248 = FStar_Syntax_Subst.compress t_norm  in
                    uu____7248.FStar_Syntax_Syntax.n  in
                  match uu____7247 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7254) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____7292  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____7299 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____7301 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____7301 with
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
                    let uu____7333 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____7333, env1)
              else
                (let uu____7338 = prims.is lid  in
                 if uu____7338
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____7347 = prims.mk lid vname  in
                   match uu____7347 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____7371 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____7371, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____7380 =
                      let uu____7399 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7399 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7427 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7427
                            then
                              let uu____7432 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___311_7435 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___311_7435.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___311_7435.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___311_7435.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___311_7435.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___311_7435.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___311_7435.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___311_7435.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___311_7435.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___311_7435.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___311_7435.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___311_7435.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___311_7435.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___311_7435.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___311_7435.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___311_7435.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___311_7435.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___311_7435.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___311_7435.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___311_7435.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___311_7435.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___311_7435.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___311_7435.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___311_7435.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___311_7435.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___311_7435.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___311_7435.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___311_7435.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___311_7435.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___311_7435.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___311_7435.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___311_7435.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___311_7435.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___311_7435.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___311_7435.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___311_7435.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___311_7435.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___311_7435.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___311_7435.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___311_7435.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___311_7435.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___311_7435.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___311_7435.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7432
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7458 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7458)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____7380 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7564  ->
                                  match uu___0_7564 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7568 = FStar_Util.prefix vars
                                         in
                                      (match uu____7568 with
                                       | (uu____7601,xxv) ->
                                           let xx =
                                             let uu____7640 =
                                               let uu____7641 =
                                                 let uu____7647 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7647,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7641
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7640
                                              in
                                           let uu____7650 =
                                             let uu____7651 =
                                               let uu____7659 =
                                                 let uu____7660 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7661 =
                                                   let uu____7672 =
                                                     let uu____7673 =
                                                       let uu____7678 =
                                                         let uu____7679 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7679
                                                          in
                                                       (vapp, uu____7678)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7673
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7672)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7660 uu____7661
                                                  in
                                               (uu____7659,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7651
                                              in
                                           [uu____7650])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7694 = FStar_Util.prefix vars
                                         in
                                      (match uu____7694 with
                                       | (uu____7727,xxv) ->
                                           let xx =
                                             let uu____7766 =
                                               let uu____7767 =
                                                 let uu____7773 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7773,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7767
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7766
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
                                           let uu____7784 =
                                             let uu____7785 =
                                               let uu____7793 =
                                                 let uu____7794 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7795 =
                                                   let uu____7806 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7806)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7794 uu____7795
                                                  in
                                               (uu____7793,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7785
                                              in
                                           [uu____7784])
                                  | uu____7819 -> []))
                           in
                        let uu____7820 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7820 with
                         | (vars,guards,env',decls1,uu____7845) ->
                             let uu____7858 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7871 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7871, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7875 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7875 with
                                    | (g,ds) ->
                                        let uu____7888 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7888,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7858 with
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
                                  let should_thunk uu____7911 =
                                    let is_type1 t =
                                      let uu____7919 =
                                        let uu____7920 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7920.FStar_Syntax_Syntax.n  in
                                      match uu____7919 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7924 -> true
                                      | uu____7926 -> false  in
                                    let is_squash1 t =
                                      let uu____7935 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7935 with
                                      | (head1,uu____7954) ->
                                          let uu____7979 =
                                            let uu____7980 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____7980.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7979 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____7985;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____7986;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____7988;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____7989;_};_},uu____7990)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7998 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____8003 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____8003))
                                       &&
                                       (let uu____8009 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____8009))
                                      &&
                                      (let uu____8012 = is_type1 t_norm  in
                                       Prims.op_Negation uu____8012)
                                     in
                                  let uu____8014 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____8073 -> (false, vars)  in
                                  (match uu____8014 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____8123 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____8123 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____8155 =
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
                                              | uu____8176 ->
                                                  let uu____8185 =
                                                    let uu____8193 =
                                                      get_vtok ()  in
                                                    (uu____8193, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8185
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____8200 =
                                                let uu____8208 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____8208)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____8200
                                               in
                                            let uu____8222 =
                                              let vname_decl =
                                                let uu____8230 =
                                                  let uu____8242 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____8242,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____8230
                                                 in
                                              let uu____8253 =
                                                let env2 =
                                                  let uu___406_8259 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___406_8259.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____8260 =
                                                  let uu____8262 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____8262
                                                   in
                                                if uu____8260
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____8253 with
                                              | (tok_typing,decls2) ->
                                                  let uu____8279 =
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
                                                        let uu____8305 =
                                                          let uu____8308 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8308
                                                           in
                                                        let uu____8315 =
                                                          let uu____8316 =
                                                            let uu____8319 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _8325  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _8325)
                                                              uu____8319
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____8316
                                                           in
                                                        (uu____8305,
                                                          uu____8315)
                                                    | uu____8328 when thunked
                                                        -> (decls2, env1)
                                                    | uu____8341 ->
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
                                                          let uu____8365 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8366 =
                                                            let uu____8377 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8377)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8365
                                                            uu____8366
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8387 =
                                                            let uu____8395 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8395,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8387
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
                                                            let uu____8406 =
                                                              let uu____8407
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8407]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8406
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8434 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8435 =
                                                              let uu____8446
                                                                =
                                                                let uu____8447
                                                                  =
                                                                  let uu____8452
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8453
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8452,
                                                                    uu____8453)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8447
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8446)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8434
                                                              uu____8435
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8482 =
                                                          let uu____8485 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8485
                                                           in
                                                        (uu____8482, env1)
                                                     in
                                                  (match uu____8279 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8506 =
                                                         let uu____8509 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8509
                                                           tok_decl
                                                          in
                                                       (uu____8506, env2))
                                               in
                                            (match uu____8222 with
                                             | (decls2,env2) ->
                                                 let uu____8528 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8538 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8538 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8553 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8553, decls)
                                                    in
                                                 (match uu____8528 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8568 =
                                                          let uu____8576 =
                                                            let uu____8577 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8578 =
                                                              let uu____8589
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8589)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8577
                                                              uu____8578
                                                             in
                                                          (uu____8576,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8568
                                                         in
                                                      let freshness =
                                                        let uu____8605 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8605
                                                        then
                                                          let uu____8613 =
                                                            let uu____8614 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8615 =
                                                              let uu____8628
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8635
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8628,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8635)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8614
                                                              uu____8615
                                                             in
                                                          let uu____8641 =
                                                            let uu____8644 =
                                                              let uu____8645
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8645
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8644]  in
                                                          uu____8613 ::
                                                            uu____8641
                                                        else []  in
                                                      let g =
                                                        let uu____8651 =
                                                          let uu____8654 =
                                                            let uu____8657 =
                                                              let uu____8660
                                                                =
                                                                let uu____8663
                                                                  =
                                                                  let uu____8666
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8666
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8663
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8660
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8657
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8654
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8651
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
          let uu____8706 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8706 with
          | FStar_Pervasives_Native.None  ->
              let uu____8717 = encode_free_var false env x t t_norm []  in
              (match uu____8717 with
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
            let uu____8780 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8780 with
            | (decls,env1) ->
                let uu____8791 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8791
                then
                  let uu____8798 =
                    let uu____8799 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8799  in
                  (uu____8798, env1)
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
             (fun uu____8855  ->
                fun lb  ->
                  match uu____8855 with
                  | (decls,env1) ->
                      let uu____8875 =
                        let uu____8880 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8880
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8875 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8909 = FStar_Syntax_Util.head_and_args t  in
    match uu____8909 with
    | (hd1,args) ->
        let uu____8953 =
          let uu____8954 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8954.FStar_Syntax_Syntax.n  in
        (match uu____8953 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8960,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____8984 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____8995 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___490_9003 = en  in
    let uu____9004 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___490_9003.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___490_9003.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___490_9003.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___490_9003.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___490_9003.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___490_9003.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___490_9003.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___490_9003.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___490_9003.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___490_9003.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9004
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____9034  ->
      fun quals  ->
        match uu____9034 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____9139 = FStar_Util.first_N nbinders formals  in
              match uu____9139 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____9236  ->
                         fun uu____9237  ->
                           match (uu____9236, uu____9237) with
                           | ((formal,uu____9263),(binder,uu____9265)) ->
                               let uu____9286 =
                                 let uu____9293 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9293)  in
                               FStar_Syntax_Syntax.NT uu____9286) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9307 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9348  ->
                              match uu____9348 with
                              | (x,i) ->
                                  let uu____9367 =
                                    let uu___516_9368 = x  in
                                    let uu____9369 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___516_9368.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___516_9368.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9369
                                    }  in
                                  (uu____9367, i)))
                       in
                    FStar_All.pipe_right uu____9307
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9393 =
                      let uu____9398 = FStar_Syntax_Subst.compress body  in
                      let uu____9399 =
                        let uu____9400 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9400
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9398 uu____9399
                       in
                    uu____9393 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___523_9449 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___523_9449.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___523_9449.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___523_9449.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___523_9449.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___523_9449.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___523_9449.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___523_9449.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___523_9449.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___523_9449.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___523_9449.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___523_9449.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___523_9449.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___523_9449.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___523_9449.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___523_9449.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___523_9449.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___523_9449.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___523_9449.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___523_9449.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___523_9449.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___523_9449.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___523_9449.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___523_9449.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___523_9449.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___523_9449.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___523_9449.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___523_9449.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___523_9449.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___523_9449.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___523_9449.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___523_9449.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___523_9449.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___523_9449.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___523_9449.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___523_9449.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___523_9449.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___523_9449.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___523_9449.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___523_9449.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___523_9449.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___523_9449.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___523_9449.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9521  ->
                       fun uu____9522  ->
                         match (uu____9521, uu____9522) with
                         | ((x,uu____9548),(b,uu____9550)) ->
                             let uu____9571 =
                               let uu____9578 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9578)  in
                             FStar_Syntax_Syntax.NT uu____9571) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9603 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9603
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9632 ->
                    let uu____9639 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9639
                | uu____9640 when Prims.op_Negation norm1 ->
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
                | uu____9643 ->
                    let uu____9644 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9644)
                 in
              let aux t1 e1 =
                let uu____9686 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9686 with
                | (binders,body,lopt) ->
                    let uu____9718 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9734 -> arrow_formals_comp_norm false t1  in
                    (match uu____9718 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9768 =
                           if nformals < nbinders
                           then
                             let uu____9802 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9802 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9882 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9882)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9912 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9912 with
                                | (binders1,body1) ->
                                    let uu____9965 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____9965))
                             else
                               (let uu____9978 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____9978))
                            in
                         (match uu____9768 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10038 = aux t e  in
              match uu____10038 with
              | (binders,body,comp) ->
                  let uu____10084 =
                    let uu____10095 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____10095
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____10110 = aux comp1 body1  in
                      match uu____10110 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10084 with
                   | (binders1,body1,comp1) ->
                       let uu____10193 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10193, comp1))
               in
            (try
               (fun uu___593_10220  ->
                  match () with
                  | () ->
                      let uu____10227 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10227
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10243 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10306  ->
                                   fun lb  ->
                                     match uu____10306 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10361 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10361
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10367 =
                                             let uu____10376 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10376
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10367 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10243 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10517;
                                    FStar_Syntax_Syntax.lbeff = uu____10518;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10520;
                                    FStar_Syntax_Syntax.lbpos = uu____10521;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10545 =
                                     let uu____10552 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10552 with
                                     | (tcenv',uu____10568,e_t) ->
                                         let uu____10574 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10585 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10574 with
                                          | (e1,t_norm1) ->
                                              ((let uu___656_10602 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___656_10602.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10545 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10612 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10612 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10632 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10632
                                               then
                                                 let uu____10637 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10640 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10637 uu____10640
                                               else ());
                                              (let uu____10645 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10645 with
                                               | (vars,_guards,env'1,binder_decls,uu____10672)
                                                   ->
                                                   let uu____10685 =
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
                                                         let uu____10702 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10702
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10724 =
                                                          let uu____10725 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10726 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10725 fvb
                                                            uu____10726
                                                           in
                                                        (vars, uu____10724))
                                                      in
                                                   (match uu____10685 with
                                                    | (vars1,app) ->
                                                        let uu____10737 =
                                                          let is_logical =
                                                            let uu____10750 =
                                                              let uu____10751
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10751.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10750
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10757 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10761 =
                                                              let uu____10762
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10762
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10761
                                                              (fun lid  ->
                                                                 let uu____10771
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10771
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10772 =
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
                                                          if uu____10772
                                                          then
                                                            let uu____10788 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10789 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10788,
                                                              uu____10789)
                                                          else
                                                            (let uu____10800
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10800))
                                                           in
                                                        (match uu____10737
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10824
                                                                 =
                                                                 let uu____10832
                                                                   =
                                                                   let uu____10833
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10834
                                                                    =
                                                                    let uu____10845
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10845)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10833
                                                                    uu____10834
                                                                    in
                                                                 let uu____10854
                                                                   =
                                                                   let uu____10855
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10855
                                                                    in
                                                                 (uu____10832,
                                                                   uu____10854,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10824
                                                                in
                                                             let uu____10861
                                                               =
                                                               let uu____10864
                                                                 =
                                                                 let uu____10867
                                                                   =
                                                                   let uu____10870
                                                                    =
                                                                    let uu____10873
                                                                    =
                                                                    let uu____10876
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10876
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10873
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10870
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10867
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10864
                                                                in
                                                             (uu____10861,
                                                               env2)))))))
                               | uu____10885 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10945 =
                                   let uu____10951 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10951,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10945  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10957 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11010  ->
                                         fun fvb  ->
                                           match uu____11010 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11065 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11065
                                                  in
                                               let gtok =
                                                 let uu____11069 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11069
                                                  in
                                               let env4 =
                                                 let uu____11072 =
                                                   let uu____11075 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _11081  ->
                                                        FStar_Pervasives_Native.Some
                                                          _11081) uu____11075
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11072
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10957 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11201
                                     t_norm uu____11203 =
                                     match (uu____11201, uu____11203) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11233;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11234;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11236;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11237;_})
                                         ->
                                         let uu____11264 =
                                           let uu____11271 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11271 with
                                           | (tcenv',uu____11287,e_t) ->
                                               let uu____11293 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11304 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11293 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___743_11321 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___743_11321.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11264 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11334 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11334
                                                then
                                                  let uu____11339 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11341 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11343 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11339 uu____11341
                                                    uu____11343
                                                else ());
                                               (let uu____11348 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11348 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11375 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11375 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11397 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11397
                                                           then
                                                             let uu____11402
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11404
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11407
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11409
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11402
                                                               uu____11404
                                                               uu____11407
                                                               uu____11409
                                                           else ());
                                                          (let uu____11414 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11414
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11443)
                                                               ->
                                                               let uu____11456
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11469
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11469,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11473
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11473
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11486
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11486,
                                                                    decls0))
                                                                  in
                                                               (match uu____11456
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
                                                                    let uu____11507
                                                                    =
                                                                    let uu____11519
                                                                    =
                                                                    let uu____11522
                                                                    =
                                                                    let uu____11525
                                                                    =
                                                                    let uu____11528
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11528
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11525
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11522
                                                                     in
                                                                    (g,
                                                                    uu____11519,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11507
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
                                                                    let uu____11558
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11558
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
                                                                    let uu____11573
                                                                    =
                                                                    let uu____11576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11576
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11573
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11582
                                                                    =
                                                                    let uu____11585
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11585
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11582
                                                                     in
                                                                    let uu____11590
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11590
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11606
                                                                    =
                                                                    let uu____11614
                                                                    =
                                                                    let uu____11615
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11616
                                                                    =
                                                                    let uu____11632
                                                                    =
                                                                    let uu____11633
                                                                    =
                                                                    let uu____11638
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11638)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11633
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11632)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11615
                                                                    uu____11616
                                                                     in
                                                                    let uu____11652
                                                                    =
                                                                    let uu____11653
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11653
                                                                     in
                                                                    (uu____11614,
                                                                    uu____11652,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11606
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11660
                                                                    =
                                                                    let uu____11668
                                                                    =
                                                                    let uu____11669
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11670
                                                                    =
                                                                    let uu____11681
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11681)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11669
                                                                    uu____11670
                                                                     in
                                                                    (uu____11668,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11660
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11695
                                                                    =
                                                                    let uu____11703
                                                                    =
                                                                    let uu____11704
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11705
                                                                    =
                                                                    let uu____11716
                                                                    =
                                                                    let uu____11717
                                                                    =
                                                                    let uu____11722
                                                                    =
                                                                    let uu____11723
                                                                    =
                                                                    let uu____11726
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____11726
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11723
                                                                     in
                                                                    (gsapp,
                                                                    uu____11722)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11717
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11716)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11704
                                                                    uu____11705
                                                                     in
                                                                    (uu____11703,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11695
                                                                     in
                                                                    let uu____11740
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
                                                                    let uu____11752
                                                                    =
                                                                    let uu____11753
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11753
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11752
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head1
                                                                    =
                                                                    let uu____11757
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11757
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11766
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11767
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head1
                                                                    vars1
                                                                    guards1
                                                                    uu____11767
                                                                     in
                                                                    let uu____11769
                                                                    =
                                                                    let uu____11777
                                                                    =
                                                                    let uu____11778
                                                                    =
                                                                    let uu____11783
                                                                    =
                                                                    let uu____11784
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11785
                                                                    =
                                                                    let uu____11796
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11796)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11784
                                                                    uu____11785
                                                                     in
                                                                    (uu____11783,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11778
                                                                     in
                                                                    (uu____11777,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11769
                                                                     in
                                                                    let uu____11809
                                                                    =
                                                                    let uu____11818
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11818
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11833
                                                                    =
                                                                    let uu____11836
                                                                    =
                                                                    let uu____11837
                                                                    =
                                                                    let uu____11845
                                                                    =
                                                                    let uu____11846
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11847
                                                                    =
                                                                    let uu____11858
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11858)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11846
                                                                    uu____11847
                                                                     in
                                                                    (uu____11845,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11837
                                                                     in
                                                                    [uu____11836]
                                                                     in
                                                                    (d3,
                                                                    uu____11833)
                                                                     in
                                                                    match uu____11809
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11740
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11915
                                                                    =
                                                                    let uu____11918
                                                                    =
                                                                    let uu____11921
                                                                    =
                                                                    let uu____11924
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11924
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11921
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11918
                                                                     in
                                                                    let uu____11931
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11915,
                                                                    uu____11931,
                                                                    env02))))))))))
                                      in
                                   let uu____11936 =
                                     let uu____11949 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12012  ->
                                          fun uu____12013  ->
                                            match (uu____12012, uu____12013)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12138 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12138 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11949
                                      in
                                   (match uu____11936 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12205 =
                                          let isDeclFun uu___1_12222 =
                                            match uu___1_12222 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12224 -> true
                                            | uu____12237 -> false  in
                                          let uu____12239 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12239
                                            (fun decls3  ->
                                               let uu____12269 =
                                                 FStar_List.fold_left
                                                   (fun uu____12300  ->
                                                      fun elt  ->
                                                        match uu____12300
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12341 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12341
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12369
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12369
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
                                                                    let uu___841_12407
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___841_12407.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___841_12407.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___841_12407.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12269 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12439 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12439, elts, rest))
                                           in
                                        (match uu____12205 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12468 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12474  ->
                                        match uu___2_12474 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12477 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12485 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12485)))
                                in
                             if uu____12468
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___858_12507  ->
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
                   let uu____12546 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12546
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12565 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12565, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12621 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12621 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12627 = encode_sigelt' env se  in
      match uu____12627 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12639 =
                  let uu____12642 =
                    let uu____12643 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12643  in
                  [uu____12642]  in
                FStar_All.pipe_right uu____12639
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12648 ->
                let uu____12649 =
                  let uu____12652 =
                    let uu____12655 =
                      let uu____12656 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12656  in
                    [uu____12655]  in
                  FStar_All.pipe_right uu____12652
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12663 =
                  let uu____12666 =
                    let uu____12669 =
                      let uu____12672 =
                        let uu____12673 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12673  in
                      [uu____12672]  in
                    FStar_All.pipe_right uu____12669
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12666  in
                FStar_List.append uu____12649 uu____12663
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12687 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12687
       then
         let uu____12692 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12692
       else ());
      (let is_opaque_to_smt t =
         let uu____12704 =
           let uu____12705 = FStar_Syntax_Subst.compress t  in
           uu____12705.FStar_Syntax_Syntax.n  in
         match uu____12704 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12710)) -> s = "opaque_to_smt"
         | uu____12715 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12724 =
           let uu____12725 = FStar_Syntax_Subst.compress t  in
           uu____12725.FStar_Syntax_Syntax.n  in
         match uu____12724 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12730)) -> s = "uninterpreted_by_smt"
         | uu____12735 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12741 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____12747 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12759 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12760 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12761 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12774 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12776 =
             let uu____12778 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12778  in
           if uu____12776
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12807 ->
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
                  let uu____12840 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12840  in
                let uu____12841 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12841 with
                | (formals,uu____12861) ->
                    let arity = FStar_List.length formals  in
                    let uu____12885 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12885 with
                     | (aname,atok,env2) ->
                         let uu____12907 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____12907 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____12923 =
                                  let uu____12924 =
                                    let uu____12936 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____12956  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____12936,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____12924
                                   in
                                [uu____12923;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____12973 =
                                let aux uu____13019 uu____13020 =
                                  match (uu____13019, uu____13020) with
                                  | ((bv,uu____13064),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13096 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13096 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13119 =
                                             let uu____13122 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13122 :: acc_sorts  in
                                           (env4, uu____13119, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____12973 with
                               | (uu____13154,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13170 =
                                       let uu____13178 =
                                         let uu____13179 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13180 =
                                           let uu____13191 =
                                             let uu____13192 =
                                               let uu____13197 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13197)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13192
                                              in
                                           ([[app]], xs_sorts, uu____13191)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13179 uu____13180
                                          in
                                       (uu____13178,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13170
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13212 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13212
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13215 =
                                       let uu____13223 =
                                         let uu____13224 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13225 =
                                           let uu____13236 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13236)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13224 uu____13225
                                          in
                                       (uu____13223,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13215
                                      in
                                   let uu____13249 =
                                     let uu____13252 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13252  in
                                   (env2, uu____13249))))
                 in
              let uu____13261 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13261 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13287,uu____13288)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13289 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____13289 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13311,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13318 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13324  ->
                       match uu___3_13324 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13327 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13333 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13336 -> false))
                in
             Prims.op_Negation uu____13318  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13346 =
                let uu____13351 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13351 env fv t quals  in
              match uu____13346 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13365 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13365  in
                  let uu____13368 =
                    let uu____13369 =
                      let uu____13372 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13372
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13369  in
                  (uu____13368, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13382 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13382 with
            | (uvs,f1) ->
                let env1 =
                  let uu___995_13394 = env  in
                  let uu____13395 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___995_13394.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___995_13394.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___995_13394.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13395;
                    FStar_SMTEncoding_Env.warn =
                      (uu___995_13394.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___995_13394.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___995_13394.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___995_13394.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___995_13394.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___995_13394.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___995_13394.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13397 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13397 with
                 | (f3,decls) ->
                     let g =
                       let uu____13411 =
                         let uu____13414 =
                           let uu____13415 =
                             let uu____13423 =
                               let uu____13424 =
                                 let uu____13426 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13426
                                  in
                               FStar_Pervasives_Native.Some uu____13424  in
                             let uu____13430 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13423, uu____13430)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13415  in
                         [uu____13414]  in
                       FStar_All.pipe_right uu____13411
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13439) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13453 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13475 =
                        let uu____13478 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13478.FStar_Syntax_Syntax.fv_name  in
                      uu____13475.FStar_Syntax_Syntax.v  in
                    let uu____13479 =
                      let uu____13481 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13481  in
                    if uu____13479
                    then
                      let val_decl =
                        let uu___1012_13513 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1012_13513.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1012_13513.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1012_13513.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____13514 = encode_sigelt' env1 val_decl  in
                      match uu____13514 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13453 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13550,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13552;
                           FStar_Syntax_Syntax.lbtyp = uu____13553;
                           FStar_Syntax_Syntax.lbeff = uu____13554;
                           FStar_Syntax_Syntax.lbdef = uu____13555;
                           FStar_Syntax_Syntax.lbattrs = uu____13556;
                           FStar_Syntax_Syntax.lbpos = uu____13557;_}::[]),uu____13558)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13577 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____13577 with
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
                  let uu____13615 =
                    let uu____13618 =
                      let uu____13619 =
                        let uu____13627 =
                          let uu____13628 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13629 =
                            let uu____13640 =
                              let uu____13641 =
                                let uu____13646 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13646)  in
                              FStar_SMTEncoding_Util.mkEq uu____13641  in
                            ([[b2t_x]], [xx], uu____13640)  in
                          FStar_SMTEncoding_Term.mkForall uu____13628
                            uu____13629
                           in
                        (uu____13627,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13619  in
                    [uu____13618]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13615
                   in
                let uu____13684 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13684, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13687,uu____13688) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13698  ->
                   match uu___4_13698 with
                   | FStar_Syntax_Syntax.Discriminator uu____13700 -> true
                   | uu____13702 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13704,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13716 =
                      let uu____13718 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13718.FStar_Ident.idText  in
                    uu____13716 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13725  ->
                      match uu___5_13725 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13728 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13731) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13745  ->
                   match uu___6_13745 with
                   | FStar_Syntax_Syntax.Projector uu____13747 -> true
                   | uu____13753 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13757 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13757 with
            | FStar_Pervasives_Native.Some uu____13764 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1077_13766 = se  in
                  let uu____13767 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13767;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1077_13766.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1077_13766.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1077_13766.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13770) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1089_13791 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1089_13791.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1089_13791.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1089_13791.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1089_13791.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1089_13791.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13796) ->
           let uu____13805 = encode_sigelts env ses  in
           (match uu____13805 with
            | (g,env1) ->
                let uu____13816 =
                  FStar_List.fold_left
                    (fun uu____13840  ->
                       fun elt  ->
                         match uu____13840 with
                         | (g',inversions) ->
                             let uu____13868 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13891  ->
                                       match uu___7_13891 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13893;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13894;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13895;_}
                                           -> false
                                       | uu____13902 -> true))
                                in
                             (match uu____13868 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1115_13927 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1115_13927.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1115_13927.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1115_13927.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13816 with
                 | (g',inversions) ->
                     let uu____13946 =
                       FStar_List.fold_left
                         (fun uu____13977  ->
                            fun elt  ->
                              match uu____13977 with
                              | (decls,elts,rest) ->
                                  let uu____14018 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14027  ->
                                            match uu___8_14027 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14029 -> true
                                            | uu____14042 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14018
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14065 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14086  ->
                                               match uu___9_14086 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14088 -> true
                                               | uu____14101 -> false))
                                        in
                                     match uu____14065 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1137_14132 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1137_14132.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1137_14132.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1137_14132.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____13946 with
                      | (decls,elts,rest) ->
                          let uu____14158 =
                            let uu____14159 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14166 =
                              let uu____14169 =
                                let uu____14172 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14172  in
                              FStar_List.append elts uu____14169  in
                            FStar_List.append uu____14159 uu____14166  in
                          (uu____14158, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14183,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14196 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14196 with
             | (usubst,uvs) ->
                 let uu____14216 =
                   let uu____14223 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14224 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14225 =
                     let uu____14226 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14226 k  in
                   (uu____14223, uu____14224, uu____14225)  in
                 (match uu____14216 with
                  | (env1,tps1,k1) ->
                      let uu____14239 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14239 with
                       | (tps2,k2) ->
                           let uu____14247 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14247 with
                            | (uu____14263,k3) ->
                                let uu____14285 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14285 with
                                 | (tps3,env_tps,uu____14297,us) ->
                                     let u_k =
                                       let uu____14300 =
                                         let uu____14301 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14302 =
                                           let uu____14307 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  (Prims.parse_int "0"))
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14309 =
                                             let uu____14310 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14310
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14307 uu____14309
                                            in
                                         uu____14302
                                           FStar_Pervasives_Native.None
                                           uu____14301
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14300 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14328) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14334,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14337) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____14345,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14352) ->
                                           let uu____14353 =
                                             let uu____14355 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14355
                                              in
                                           failwith uu____14353
                                       | (uu____14359,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14360 =
                                             let uu____14362 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14362
                                              in
                                           failwith uu____14360
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14366,uu____14367) ->
                                           let uu____14376 =
                                             let uu____14378 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14378
                                              in
                                           failwith uu____14376
                                       | (uu____14382,FStar_Syntax_Syntax.U_unif
                                          uu____14383) ->
                                           let uu____14392 =
                                             let uu____14394 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14394
                                              in
                                           failwith uu____14392
                                       | uu____14398 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14411 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14411 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14429 = u_leq_u_k u_tp  in
                                       if uu____14429
                                       then true
                                       else
                                         (let uu____14436 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14436 with
                                          | (formals,uu____14453) ->
                                              let uu____14474 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14474 with
                                               | (uu____14484,uu____14485,uu____14486,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14497 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14497
             then
               let uu____14502 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14502
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14522  ->
                       match uu___10_14522 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14526 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14539 = c  in
                 match uu____14539 with
                 | (name,args,uu____14544,uu____14545,uu____14546) ->
                     let uu____14557 =
                       let uu____14558 =
                         let uu____14570 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14597  ->
                                   match uu____14597 with
                                   | (uu____14606,sort,uu____14608) -> sort))
                            in
                         (name, uu____14570,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14558  in
                     [uu____14557]
               else
                 (let uu____14619 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14619 c)
                in
             let inversion_axioms tapp vars =
               let uu____14637 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14645 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14645 FStar_Option.isNone))
                  in
               if uu____14637
               then []
               else
                 (let uu____14680 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14680 with
                  | (xxsym,xx) ->
                      let uu____14693 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14732  ->
                                fun l  ->
                                  match uu____14732 with
                                  | (out,decls) ->
                                      let uu____14752 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14752 with
                                       | (uu____14763,data_t) ->
                                           let uu____14765 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14765 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14809 =
                                                    let uu____14810 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14810.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14809 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14813,indices)
                                                      -> indices
                                                  | uu____14839 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14869  ->
                                                            match uu____14869
                                                            with
                                                            | (x,uu____14877)
                                                                ->
                                                                let uu____14882
                                                                  =
                                                                  let uu____14883
                                                                    =
                                                                    let uu____14891
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14891,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14883
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14882)
                                                       env)
                                                   in
                                                let uu____14896 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14896 with
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
                                                                  let uu____14931
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____14936,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____14931)
                                                             vars indices1
                                                         else []  in
                                                       let uu____14939 =
                                                         let uu____14940 =
                                                           let uu____14945 =
                                                             let uu____14946
                                                               =
                                                               let uu____14951
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____14952
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____14951,
                                                                 uu____14952)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____14946
                                                              in
                                                           (out, uu____14945)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____14940
                                                          in
                                                       (uu____14939,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14693 with
                       | (data_ax,decls) ->
                           let uu____14967 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____14967 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        (Prims.parse_int "1")
                                    then
                                      let uu____14984 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____14984 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____14991 =
                                    let uu____14999 =
                                      let uu____15000 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15001 =
                                        let uu____15012 =
                                          let uu____15013 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15015 =
                                            let uu____15018 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15018 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15013 uu____15015
                                           in
                                        let uu____15020 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15012,
                                          uu____15020)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15000 uu____15001
                                       in
                                    let uu____15029 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____14999,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15029)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____14991
                                   in
                                let uu____15035 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15035)))
                in
             let uu____15042 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15064 ->
                     let uu____15065 =
                       let uu____15072 =
                         let uu____15073 =
                           let uu____15088 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15088)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15073  in
                       FStar_Syntax_Syntax.mk uu____15072  in
                     uu____15065 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15042 with
             | (formals,res) ->
                 let uu____15128 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15128 with
                  | (vars,guards,env',binder_decls,uu____15153) ->
                      let arity = FStar_List.length vars  in
                      let uu____15167 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15167 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15193 =
                               let uu____15201 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15201)  in
                             FStar_SMTEncoding_Util.mkApp uu____15193  in
                           let uu____15207 =
                             let tname_decl =
                               let uu____15217 =
                                 let uu____15218 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15237 =
                                             let uu____15239 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15239
                                              in
                                           let uu____15241 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15237, uu____15241, false)))
                                    in
                                 let uu____15245 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15218,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15245, false)
                                  in
                               constructor_or_logic_type_decl uu____15217  in
                             let uu____15253 =
                               match vars with
                               | [] ->
                                   let uu____15266 =
                                     let uu____15267 =
                                       let uu____15270 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _15276  ->
                                            FStar_Pervasives_Native.Some
                                              _15276) uu____15270
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15267
                                      in
                                   ([], uu____15266)
                               | uu____15279 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15289 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15289
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15305 =
                                       let uu____15313 =
                                         let uu____15314 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15315 =
                                           let uu____15331 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15331)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15314 uu____15315
                                          in
                                       (uu____15313,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15305
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15253 with
                             | (tok_decls,env2) ->
                                 let uu____15358 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15358
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15207 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15386 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15386 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            (Prims.parse_int "0")
                                        then
                                          let uu____15408 =
                                            let uu____15409 =
                                              let uu____15417 =
                                                let uu____15418 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15418
                                                 in
                                              (uu____15417,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15409
                                             in
                                          [uu____15408]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15428 =
                                          FStar_List.map
                                            (fun uu____15432  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15428 true
                                         in
                                      let uu____15434 =
                                        let uu____15437 =
                                          let uu____15440 =
                                            let uu____15443 =
                                              let uu____15444 =
                                                let uu____15452 =
                                                  let uu____15453 =
                                                    let uu____15458 =
                                                      let uu____15459 =
                                                        let uu____15470 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15470)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15459
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15458)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15453
                                                   in
                                                (uu____15452,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15444
                                               in
                                            [uu____15443]  in
                                          FStar_List.append karr uu____15440
                                           in
                                        FStar_All.pipe_right uu____15437
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15434
                                   in
                                let aux =
                                  let uu____15489 =
                                    let uu____15492 =
                                      inversion_axioms tapp vars  in
                                    let uu____15495 =
                                      let uu____15498 =
                                        let uu____15501 =
                                          let uu____15502 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15502 env2 tapp
                                            vars
                                           in
                                        [uu____15501]  in
                                      FStar_All.pipe_right uu____15498
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15492 uu____15495
                                     in
                                  FStar_List.append kindingAx uu____15489  in
                                let g =
                                  let uu____15510 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15510
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15518,uu____15519,uu____15520,uu____15521,uu____15522)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15530,t,uu____15532,n_tps,uu____15534) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15545 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15545 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15593 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15593 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15617 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15617 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15637 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15637 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15716 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15716,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15723 =
                                   let uu____15724 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15724, true)
                                    in
                                 let uu____15732 =
                                   let uu____15739 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15739
                                    in
                                 FStar_All.pipe_right uu____15723 uu____15732
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
                               let uu____15751 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15751 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15763::uu____15764 ->
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
                                            let uu____15813 =
                                              let uu____15814 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15814]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15813
                                             in
                                          let uu____15840 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15841 =
                                            let uu____15852 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15852)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15840 uu____15841
                                      | uu____15879 -> tok_typing  in
                                    let uu____15890 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15890 with
                                     | (vars',guards',env'',decls_formals,uu____15915)
                                         ->
                                         let uu____15928 =
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
                                         (match uu____15928 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____15958 ->
                                                    let uu____15967 =
                                                      let uu____15968 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____15968
                                                       in
                                                    [uu____15967]
                                                 in
                                              let encode_elim uu____15984 =
                                                let uu____15985 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____15985 with
                                                | (head1,args) ->
                                                    let uu____16036 =
                                                      let uu____16037 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____16037.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16036 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16049;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16050;_},uu____16051)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16057 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16057
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
                                                                  | uu____16120
                                                                    ->
                                                                    let uu____16121
                                                                    =
                                                                    let uu____16127
                                                                    =
                                                                    let uu____16129
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16129
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16127)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16121
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16152
                                                                    =
                                                                    let uu____16154
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16154
                                                                     in
                                                                    if
                                                                    uu____16152
                                                                    then
                                                                    let uu____16176
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16176]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16179
                                                                =
                                                                let uu____16193
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16250
                                                                     ->
                                                                    fun
                                                                    uu____16251
                                                                     ->
                                                                    match 
                                                                    (uu____16250,
                                                                    uu____16251)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16362
                                                                    =
                                                                    let uu____16370
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16370
                                                                     in
                                                                    (match uu____16362
                                                                    with
                                                                    | 
                                                                    (uu____16384,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16395
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16395
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16400
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16400
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
                                                                  uu____16193
                                                                 in
                                                              (match uu____16179
                                                               with
                                                               | (uu____16421,arg_vars,elim_eqns_or_guards,uu____16424)
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
                                                                    let uu____16451
                                                                    =
                                                                    let uu____16459
                                                                    =
                                                                    let uu____16460
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16461
                                                                    =
                                                                    let uu____16472
                                                                    =
                                                                    let uu____16473
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16473
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16475
                                                                    =
                                                                    let uu____16476
                                                                    =
                                                                    let uu____16481
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16481)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16476
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16472,
                                                                    uu____16475)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16460
                                                                    uu____16461
                                                                     in
                                                                    (uu____16459,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16451
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16496
                                                                    =
                                                                    let uu____16497
                                                                    =
                                                                    let uu____16503
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16503,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16497
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16496
                                                                     in
                                                                    let uu____16506
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16506
                                                                    then
                                                                    let x =
                                                                    let uu____16510
                                                                    =
                                                                    let uu____16516
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16516,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16510
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16521
                                                                    =
                                                                    let uu____16529
                                                                    =
                                                                    let uu____16530
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16531
                                                                    =
                                                                    let uu____16542
                                                                    =
                                                                    let uu____16547
                                                                    =
                                                                    let uu____16550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16550]
                                                                     in
                                                                    [uu____16547]
                                                                     in
                                                                    let uu____16555
                                                                    =
                                                                    let uu____16556
                                                                    =
                                                                    let uu____16561
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16563
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16561,
                                                                    uu____16563)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16556
                                                                     in
                                                                    (uu____16542,
                                                                    [x],
                                                                    uu____16555)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16530
                                                                    uu____16531
                                                                     in
                                                                    let uu____16584
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16529,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16584)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16521
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16595
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
                                                                    (let uu____16618
                                                                    =
                                                                    let uu____16619
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16619
                                                                    dapp1  in
                                                                    [uu____16618])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16595
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16626
                                                                    =
                                                                    let uu____16634
                                                                    =
                                                                    let uu____16635
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16636
                                                                    =
                                                                    let uu____16647
                                                                    =
                                                                    let uu____16648
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16648
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16650
                                                                    =
                                                                    let uu____16651
                                                                    =
                                                                    let uu____16656
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16656)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16651
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16647,
                                                                    uu____16650)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16635
                                                                    uu____16636
                                                                     in
                                                                    (uu____16634,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16626)
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
                                                         let uu____16675 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16675
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
                                                                  | uu____16738
                                                                    ->
                                                                    let uu____16739
                                                                    =
                                                                    let uu____16745
                                                                    =
                                                                    let uu____16747
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16747
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16745)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16739
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16770
                                                                    =
                                                                    let uu____16772
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16772
                                                                     in
                                                                    if
                                                                    uu____16770
                                                                    then
                                                                    let uu____16794
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16794]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16797
                                                                =
                                                                let uu____16811
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16868
                                                                     ->
                                                                    fun
                                                                    uu____16869
                                                                     ->
                                                                    match 
                                                                    (uu____16868,
                                                                    uu____16869)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16980
                                                                    =
                                                                    let uu____16988
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16988
                                                                     in
                                                                    (match uu____16980
                                                                    with
                                                                    | 
                                                                    (uu____17002,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17013
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17013
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17018
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
                                                                  uu____16811
                                                                 in
                                                              (match uu____16797
                                                               with
                                                               | (uu____17039,arg_vars,elim_eqns_or_guards,uu____17042)
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
                                                                    let uu____17069
                                                                    =
                                                                    let uu____17077
                                                                    =
                                                                    let uu____17078
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17079
                                                                    =
                                                                    let uu____17090
                                                                    =
                                                                    let uu____17091
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17091
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17093
                                                                    =
                                                                    let uu____17094
                                                                    =
                                                                    let uu____17099
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17099)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17094
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17090,
                                                                    uu____17093)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17078
                                                                    uu____17079
                                                                     in
                                                                    (uu____17077,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17069
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____17114
                                                                    =
                                                                    let uu____17115
                                                                    =
                                                                    let uu____17121
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17121,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17115
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17114
                                                                     in
                                                                    let uu____17124
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____17124
                                                                    then
                                                                    let x =
                                                                    let uu____17128
                                                                    =
                                                                    let uu____17134
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____17134,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17128
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____17139
                                                                    =
                                                                    let uu____17147
                                                                    =
                                                                    let uu____17148
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17149
                                                                    =
                                                                    let uu____17160
                                                                    =
                                                                    let uu____17165
                                                                    =
                                                                    let uu____17168
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____17168]
                                                                     in
                                                                    [uu____17165]
                                                                     in
                                                                    let uu____17173
                                                                    =
                                                                    let uu____17174
                                                                    =
                                                                    let uu____17179
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____17181
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____17179,
                                                                    uu____17181)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17174
                                                                     in
                                                                    (uu____17160,
                                                                    [x],
                                                                    uu____17173)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17148
                                                                    uu____17149
                                                                     in
                                                                    let uu____17202
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____17147,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____17202)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17139
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____17213
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
                                                                    (let uu____17236
                                                                    =
                                                                    let uu____17237
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____17237
                                                                    dapp1  in
                                                                    [uu____17236])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17213
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17244
                                                                    =
                                                                    let uu____17252
                                                                    =
                                                                    let uu____17253
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17254
                                                                    =
                                                                    let uu____17265
                                                                    =
                                                                    let uu____17266
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17266
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17268
                                                                    =
                                                                    let uu____17269
                                                                    =
                                                                    let uu____17274
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17274)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17269
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17265,
                                                                    uu____17268)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17253
                                                                    uu____17254
                                                                     in
                                                                    (uu____17252,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17244)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17291 ->
                                                         ((let uu____17293 =
                                                             let uu____17299
                                                               =
                                                               let uu____17301
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17303
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17301
                                                                 uu____17303
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17299)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17293);
                                                          ([], [])))
                                                 in
                                              let uu____17311 =
                                                encode_elim ()  in
                                              (match uu____17311 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17337 =
                                                       let uu____17340 =
                                                         let uu____17343 =
                                                           let uu____17346 =
                                                             let uu____17349
                                                               =
                                                               let uu____17352
                                                                 =
                                                                 let uu____17355
                                                                   =
                                                                   let uu____17356
                                                                    =
                                                                    let uu____17368
                                                                    =
                                                                    let uu____17369
                                                                    =
                                                                    let uu____17371
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17371
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17369
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17368)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17356
                                                                    in
                                                                 [uu____17355]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17352
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17349
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17382 =
                                                             let uu____17385
                                                               =
                                                               let uu____17388
                                                                 =
                                                                 let uu____17391
                                                                   =
                                                                   let uu____17394
                                                                    =
                                                                    let uu____17397
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17402
                                                                    =
                                                                    let uu____17405
                                                                    =
                                                                    let uu____17406
                                                                    =
                                                                    let uu____17414
                                                                    =
                                                                    let uu____17415
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17416
                                                                    =
                                                                    let uu____17427
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17427)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17415
                                                                    uu____17416
                                                                     in
                                                                    (uu____17414,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17406
                                                                     in
                                                                    let uu____17440
                                                                    =
                                                                    let uu____17443
                                                                    =
                                                                    let uu____17444
                                                                    =
                                                                    let uu____17452
                                                                    =
                                                                    let uu____17453
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17454
                                                                    =
                                                                    let uu____17465
                                                                    =
                                                                    let uu____17466
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17466
                                                                    vars'  in
                                                                    let uu____17468
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17465,
                                                                    uu____17468)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17453
                                                                    uu____17454
                                                                     in
                                                                    (uu____17452,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17444
                                                                     in
                                                                    [uu____17443]
                                                                     in
                                                                    uu____17405
                                                                    ::
                                                                    uu____17440
                                                                     in
                                                                    uu____17397
                                                                    ::
                                                                    uu____17402
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17394
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17391
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17388
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17385
                                                              in
                                                           FStar_List.append
                                                             uu____17346
                                                             uu____17382
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17343
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17340
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17337
                                                      in
                                                   let uu____17485 =
                                                     let uu____17486 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17486 g
                                                      in
                                                   (uu____17485, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17520  ->
              fun se  ->
                match uu____17520 with
                | (g,env1) ->
                    let uu____17540 = encode_sigelt env1 se  in
                    (match uu____17540 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17608 =
        match uu____17608 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17645 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17653 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17653
                   then
                     let uu____17658 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17660 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17662 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17658 uu____17660 uu____17662
                   else ());
                  (let uu____17667 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17667 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17685 =
                         let uu____17693 =
                           let uu____17695 =
                             let uu____17697 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17697
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17695  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17693
                          in
                       (match uu____17685 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17717 = FStar_Options.log_queries ()
                                 in
                              if uu____17717
                              then
                                let uu____17720 =
                                  let uu____17722 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17724 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17726 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17722 uu____17724 uu____17726
                                   in
                                FStar_Pervasives_Native.Some uu____17720
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17742 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17752 =
                                let uu____17755 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17755  in
                              FStar_List.append uu____17742 uu____17752  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17767,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17787 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17787 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____17808 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____17808 with | (uu____17835,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17888  ->
              match uu____17888 with
              | (l,uu____17897,uu____17898) ->
                  let uu____17901 =
                    let uu____17913 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17913, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17901))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17946  ->
              match uu____17946 with
              | (l,uu____17957,uu____17958) ->
                  let uu____17961 =
                    let uu____17962 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _17965  -> FStar_SMTEncoding_Term.Echo _17965)
                      uu____17962
                     in
                  let uu____17966 =
                    let uu____17969 =
                      let uu____17970 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17970  in
                    [uu____17969]  in
                  uu____17961 :: uu____17966))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17988 =
      let uu____17991 =
        let uu____17992 = FStar_Util.psmap_empty ()  in
        let uu____18007 =
          let uu____18016 = FStar_Util.psmap_empty ()  in (uu____18016, [])
           in
        let uu____18023 =
          let uu____18025 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____18025 FStar_Ident.string_of_lid  in
        let uu____18027 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17992;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18007;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18023;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18027
        }  in
      [uu____17991]  in
    FStar_ST.op_Colon_Equals last_env uu____17988
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____18071 = FStar_ST.op_Bang last_env  in
      match uu____18071 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18099 ->
          let uu___1564_18102 = e  in
          let uu____18103 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1564_18102.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1564_18102.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1564_18102.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1564_18102.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1564_18102.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1564_18102.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1564_18102.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18103;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1564_18102.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1564_18102.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18111 = FStar_ST.op_Bang last_env  in
    match uu____18111 with
    | [] -> failwith "Empty env stack"
    | uu____18138::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____18170  ->
    let uu____18171 = FStar_ST.op_Bang last_env  in
    match uu____18171 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____18231  ->
    let uu____18232 = FStar_ST.op_Bang last_env  in
    match uu____18232 with
    | [] -> failwith "Popping an empty stack"
    | uu____18259::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18296  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18349  ->
         let uu____18350 = snapshot_env ()  in
         match uu____18350 with
         | (env_depth,()) ->
             let uu____18372 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18372 with
              | (varops_depth,()) ->
                  let uu____18394 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18394 with
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
        (fun uu____18452  ->
           let uu____18453 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18453 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18548 = snapshot msg  in () 
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
        | (uu____18594::uu____18595,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1625_18603 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1625_18603.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1625_18603.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1625_18603.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18604 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1631_18631 = elt  in
        let uu____18632 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1631_18631.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1631_18631.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18632;
          FStar_SMTEncoding_Term.a_names =
            (uu___1631_18631.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18652 =
        let uu____18655 =
          let uu____18656 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18656  in
        let uu____18657 = open_fact_db_tags env  in uu____18655 ::
          uu____18657
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18652
  
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
      let uu____18684 = encode_sigelt env se  in
      match uu____18684 with
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
                (let uu____18730 =
                   let uu____18733 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18733
                    in
                 match uu____18730 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18748 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18748
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18778 = FStar_Options.log_queries ()  in
        if uu____18778
        then
          let uu____18783 =
            let uu____18784 =
              let uu____18786 =
                let uu____18788 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18788 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18786  in
            FStar_SMTEncoding_Term.Caption uu____18784  in
          uu____18783 :: decls
        else decls  in
      (let uu____18807 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18807
       then
         let uu____18810 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18810
       else ());
      (let env =
         let uu____18816 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18816 tcenv  in
       let uu____18817 = encode_top_level_facts env se  in
       match uu____18817 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18831 =
               let uu____18834 =
                 let uu____18837 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18837
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18834  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18831)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18870 = FStar_Options.log_queries ()  in
          if uu____18870
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1669_18890 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1669_18890.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1669_18890.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1669_18890.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1669_18890.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1669_18890.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1669_18890.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1669_18890.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1669_18890.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1669_18890.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1669_18890.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18895 =
             let uu____18898 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18898
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18895  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18918 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18918
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
          (let uu____18942 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18942
           then
             let uu____18945 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18945
           else ());
          (let env =
             let uu____18953 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18953
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18992  ->
                     fun se  ->
                       match uu____18992 with
                       | (g,env2) ->
                           let uu____19012 = encode_top_level_facts env2 se
                              in
                           (match uu____19012 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____19035 =
             encode_signature
               (let uu___1692_19044 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1692_19044.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1692_19044.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1692_19044.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1692_19044.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1692_19044.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1692_19044.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1692_19044.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1692_19044.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1692_19044.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1692_19044.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____19035 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19060 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19060
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____19066 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____19066))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____19094  ->
        match uu____19094 with
        | (decls,fvbs) ->
            ((let uu____19108 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____19108
              then ()
              else
                (let uu____19113 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19113
                 then
                   let uu____19116 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____19116
                 else ()));
             (let env =
                let uu____19124 = get_env name tcenv  in
                FStar_All.pipe_right uu____19124
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____19126 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____19126
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____19140 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____19140
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
        (let uu____19202 =
           let uu____19204 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____19204.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19202);
        (let env =
           let uu____19206 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19206 tcenv  in
         let uu____19207 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19246 = aux rest  in
                 (match uu____19246 with
                  | (out,rest1) ->
                      let t =
                        let uu____19274 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19274 with
                        | FStar_Pervasives_Native.Some uu____19277 ->
                            let uu____19278 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19278
                              x.FStar_Syntax_Syntax.sort
                        | uu____19279 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19283 =
                        let uu____19286 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1733_19289 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1733_19289.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1733_19289.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19286 :: out  in
                      (uu____19283, rest1))
             | uu____19294 -> ([], bindings)  in
           let uu____19301 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19301 with
           | (closing,bindings) ->
               let uu____19328 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19328, bindings)
            in
         match uu____19207 with
         | (q1,bindings) ->
             let uu____19359 = encode_env_bindings env bindings  in
             (match uu____19359 with
              | (env_decls,env1) ->
                  ((let uu____19381 =
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
                    if uu____19381
                    then
                      let uu____19388 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____19388
                    else ());
                   (let uu____19393 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____19393 with
                    | (phi,qdecls) ->
                        let uu____19414 =
                          let uu____19419 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19419 phi
                           in
                        (match uu____19414 with
                         | (labels,phi1) ->
                             let uu____19436 = encode_labels labels  in
                             (match uu____19436 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19472 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19472
                                    then
                                      let uu____19477 =
                                        let uu____19478 =
                                          let uu____19480 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19480
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19478
                                         in
                                      [uu____19477]
                                    else []  in
                                  let query_prelude =
                                    let uu____19488 =
                                      let uu____19489 =
                                        let uu____19490 =
                                          let uu____19493 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19500 =
                                            let uu____19503 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19503
                                             in
                                          FStar_List.append uu____19493
                                            uu____19500
                                           in
                                        FStar_List.append env_decls
                                          uu____19490
                                         in
                                      FStar_All.pipe_right uu____19489
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19488
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19513 =
                                      let uu____19521 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19522 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19521,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19522)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19513
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
  