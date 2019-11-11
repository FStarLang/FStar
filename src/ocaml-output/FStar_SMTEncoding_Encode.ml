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
                                    Prims.int_zero
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
                                      Prims.int_zero
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
        let uu____6285 = FStar_SMTEncoding_Term.n_fuel Prims.int_one  in
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
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu____6434)
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
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
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
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
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
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___311_7435.FStar_TypeChecker_Env.mpreprocess);
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
                                       (uu___311_7435.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___311_7435.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___311_7435.FStar_TypeChecker_Env.erasable_types_tab)
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
                                                 Prims.int_zero;
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
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___523_9449.FStar_TypeChecker_Env.mpreprocess);
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
                    (uu___523_9449.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___523_9449.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___523_9449.FStar_TypeChecker_Env.erasable_types_tab)
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
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp
                       in
                    if uu____10095
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body  in
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
                                                                    Prims.int_one)
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
                                                                    Prims.int_zero),
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
                                                                    Prims.int_zero
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
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
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
                                | FStar_SMTEncoding_Env.Inner_let_rec names1
                                    ->
                                    let plural =
                                      (FStar_List.length names1) >
                                        Prims.int_one
                                       in
                                    let r =
                                      let uu____12552 = FStar_List.hd names1
                                         in
                                      FStar_All.pipe_right uu____12552
                                        FStar_Pervasives_Native.snd
                                       in
                                    ((let uu____12570 =
                                        let uu____12580 =
                                          let uu____12588 =
                                            let uu____12590 =
                                              let uu____12592 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names1
                                                 in
                                              FStar_All.pipe_right
                                                uu____12592
                                                (FStar_String.concat ",")
                                               in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12590
                                              (if plural
                                               then "their"
                                               else "its")
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12588, r)
                                           in
                                        [uu____12580]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12570);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12651 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12651
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12670 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12670, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12726 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12726 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12732 = encode_sigelt' env se  in
      match uu____12732 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12744 =
                  let uu____12747 =
                    let uu____12748 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12748  in
                  [uu____12747]  in
                FStar_All.pipe_right uu____12744
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12753 ->
                let uu____12754 =
                  let uu____12757 =
                    let uu____12760 =
                      let uu____12761 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12761  in
                    [uu____12760]  in
                  FStar_All.pipe_right uu____12757
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12768 =
                  let uu____12771 =
                    let uu____12774 =
                      let uu____12777 =
                        let uu____12778 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12778  in
                      [uu____12777]  in
                    FStar_All.pipe_right uu____12774
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12771  in
                FStar_List.append uu____12754 uu____12768
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12792 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12792
       then
         let uu____12797 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12797
       else ());
      (let is_opaque_to_smt t =
         let uu____12809 =
           let uu____12810 = FStar_Syntax_Subst.compress t  in
           uu____12810.FStar_Syntax_Syntax.n  in
         match uu____12809 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12815)) -> s = "opaque_to_smt"
         | uu____12820 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12829 =
           let uu____12830 = FStar_Syntax_Subst.compress t  in
           uu____12830.FStar_Syntax_Syntax.n  in
         match uu____12829 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12835)) -> s = "uninterpreted_by_smt"
         | uu____12840 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____12846 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12858 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12859 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12860 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12873 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12875 =
             let uu____12877 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12877  in
           if uu____12875
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12906 ->
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
                  let uu____12939 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12939  in
                let uu____12940 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12940 with
                | (formals,uu____12960) ->
                    let arity = FStar_List.length formals  in
                    let uu____12984 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____12984 with
                     | (aname,atok,env2) ->
                         let uu____13006 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____13006 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____13022 =
                                  let uu____13023 =
                                    let uu____13035 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13055  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____13035,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____13023
                                   in
                                [uu____13022;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13072 =
                                let aux uu____13118 uu____13119 =
                                  match (uu____13118, uu____13119) with
                                  | ((bv,uu____13163),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13195 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13195 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13218 =
                                             let uu____13221 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13221 :: acc_sorts  in
                                           (env4, uu____13218, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13072 with
                               | (uu____13253,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13269 =
                                       let uu____13277 =
                                         let uu____13278 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13279 =
                                           let uu____13290 =
                                             let uu____13291 =
                                               let uu____13296 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13296)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13291
                                              in
                                           ([[app]], xs_sorts, uu____13290)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13278 uu____13279
                                          in
                                       (uu____13277,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13269
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13311 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13311
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13314 =
                                       let uu____13322 =
                                         let uu____13323 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13324 =
                                           let uu____13335 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13335)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13323 uu____13324
                                          in
                                       (uu____13322,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13314
                                      in
                                   let uu____13348 =
                                     let uu____13351 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13351  in
                                   (env2, uu____13348))))
                 in
              let uu____13360 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13360 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13386,uu____13387)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13388 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4))
              in
           (match uu____13388 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13410,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13417 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13423  ->
                       match uu___3_13423 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13426 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13432 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13435 -> false))
                in
             Prims.op_Negation uu____13417  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13445 =
                let uu____13450 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13450 env fv t quals  in
              match uu____13445 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13464 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13464  in
                  let uu____13467 =
                    let uu____13468 =
                      let uu____13471 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13471
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13468  in
                  (uu____13467, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13481 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13481 with
            | (uvs,f1) ->
                let env1 =
                  let uu___999_13493 = env  in
                  let uu____13494 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___999_13493.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___999_13493.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___999_13493.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13494;
                    FStar_SMTEncoding_Env.warn =
                      (uu___999_13493.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___999_13493.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___999_13493.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___999_13493.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___999_13493.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___999_13493.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___999_13493.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13496 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13496 with
                 | (f3,decls) ->
                     let g =
                       let uu____13510 =
                         let uu____13513 =
                           let uu____13514 =
                             let uu____13522 =
                               let uu____13523 =
                                 let uu____13525 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13525
                                  in
                               FStar_Pervasives_Native.Some uu____13523  in
                             let uu____13529 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13522, uu____13529)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13514  in
                         [uu____13513]  in
                       FStar_All.pipe_right uu____13510
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13538) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13552 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13574 =
                        let uu____13577 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13577.FStar_Syntax_Syntax.fv_name  in
                      uu____13574.FStar_Syntax_Syntax.v  in
                    let uu____13578 =
                      let uu____13580 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13580  in
                    if uu____13578
                    then
                      let val_decl =
                        let uu___1016_13612 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1016_13612.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1016_13612.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1016_13612.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1016_13612.FStar_Syntax_Syntax.sigopts)
                        }  in
                      let uu____13613 = encode_sigelt' env1 val_decl  in
                      match uu____13613 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13552 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13649,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13651;
                           FStar_Syntax_Syntax.lbtyp = uu____13652;
                           FStar_Syntax_Syntax.lbeff = uu____13653;
                           FStar_Syntax_Syntax.lbdef = uu____13654;
                           FStar_Syntax_Syntax.lbattrs = uu____13655;
                           FStar_Syntax_Syntax.lbpos = uu____13656;_}::[]),uu____13657)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13676 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one
              in
           (match uu____13676 with
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
                  let uu____13714 =
                    let uu____13717 =
                      let uu____13718 =
                        let uu____13726 =
                          let uu____13727 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13728 =
                            let uu____13739 =
                              let uu____13740 =
                                let uu____13745 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13745)  in
                              FStar_SMTEncoding_Util.mkEq uu____13740  in
                            ([[b2t_x]], [xx], uu____13739)  in
                          FStar_SMTEncoding_Term.mkForall uu____13727
                            uu____13728
                           in
                        (uu____13726,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13718  in
                    [uu____13717]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13714
                   in
                let uu____13783 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13783, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13786,uu____13787) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13797  ->
                   match uu___4_13797 with
                   | FStar_Syntax_Syntax.Discriminator uu____13799 -> true
                   | uu____13801 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13803,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13815 =
                      let uu____13817 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13817.FStar_Ident.idText  in
                    uu____13815 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13824  ->
                      match uu___5_13824 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13827 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13830) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13844  ->
                   match uu___6_13844 with
                   | FStar_Syntax_Syntax.Projector uu____13846 -> true
                   | uu____13852 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13856 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13856 with
            | FStar_Pervasives_Native.Some uu____13863 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1081_13865 = se  in
                  let uu____13866 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13866;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1081_13865.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1081_13865.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1081_13865.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1081_13865.FStar_Syntax_Syntax.sigopts)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13869) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1093_13890 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1093_13890.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1093_13890.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1093_13890.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1093_13890.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1093_13890.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13895) ->
           let uu____13904 = encode_sigelts env ses  in
           (match uu____13904 with
            | (g,env1) ->
                let uu____13915 =
                  FStar_List.fold_left
                    (fun uu____13939  ->
                       fun elt  ->
                         match uu____13939 with
                         | (g',inversions) ->
                             let uu____13967 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_13990  ->
                                       match uu___7_13990 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____13992;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____13993;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____13994;_}
                                           -> false
                                       | uu____14001 -> true))
                                in
                             (match uu____13967 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1119_14026 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1119_14026.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1119_14026.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1119_14026.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13915 with
                 | (g',inversions) ->
                     let uu____14045 =
                       FStar_List.fold_left
                         (fun uu____14076  ->
                            fun elt  ->
                              match uu____14076 with
                              | (decls,elts,rest) ->
                                  let uu____14117 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14126  ->
                                            match uu___8_14126 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14128 -> true
                                            | uu____14141 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14117
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14164 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14185  ->
                                               match uu___9_14185 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14187 -> true
                                               | uu____14200 -> false))
                                        in
                                     match uu____14164 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1141_14231 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1141_14231.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1141_14231.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1141_14231.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____14045 with
                      | (decls,elts,rest) ->
                          let uu____14257 =
                            let uu____14258 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14265 =
                              let uu____14268 =
                                let uu____14271 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14271  in
                              FStar_List.append elts uu____14268  in
                            FStar_List.append uu____14258 uu____14265  in
                          (uu____14257, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14282,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14295 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14295 with
             | (usubst,uvs) ->
                 let uu____14315 =
                   let uu____14322 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14323 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14324 =
                     let uu____14325 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14325 k  in
                   (uu____14322, uu____14323, uu____14324)  in
                 (match uu____14315 with
                  | (env1,tps1,k1) ->
                      let uu____14338 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14338 with
                       | (tps2,k2) ->
                           let uu____14346 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14346 with
                            | (uu____14362,k3) ->
                                let uu____14384 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14384 with
                                 | (tps3,env_tps,uu____14396,us) ->
                                     let u_k =
                                       let uu____14399 =
                                         let uu____14400 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14401 =
                                           let uu____14406 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  Prims.int_zero)
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14408 =
                                             let uu____14409 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14409
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14406 uu____14408
                                            in
                                         uu____14401
                                           FStar_Pervasives_Native.None
                                           uu____14400
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14399 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14427) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14433,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14436) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____14444,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14451) ->
                                           let uu____14452 =
                                             let uu____14454 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14454
                                              in
                                           failwith uu____14452
                                       | (uu____14458,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14459 =
                                             let uu____14461 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14461
                                              in
                                           failwith uu____14459
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14465,uu____14466) ->
                                           let uu____14475 =
                                             let uu____14477 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14477
                                              in
                                           failwith uu____14475
                                       | (uu____14481,FStar_Syntax_Syntax.U_unif
                                          uu____14482) ->
                                           let uu____14491 =
                                             let uu____14493 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14493
                                              in
                                           failwith uu____14491
                                       | uu____14497 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14510 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14510 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14528 = u_leq_u_k u_tp  in
                                       if uu____14528
                                       then true
                                       else
                                         (let uu____14535 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14535 with
                                          | (formals,uu____14552) ->
                                              let uu____14573 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14573 with
                                               | (uu____14583,uu____14584,uu____14585,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14596 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14596
             then
               let uu____14601 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14601
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14621  ->
                       match uu___10_14621 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14625 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14638 = c  in
                 match uu____14638 with
                 | (name,args,uu____14643,uu____14644,uu____14645) ->
                     let uu____14656 =
                       let uu____14657 =
                         let uu____14669 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14696  ->
                                   match uu____14696 with
                                   | (uu____14705,sort,uu____14707) -> sort))
                            in
                         (name, uu____14669,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14657  in
                     [uu____14656]
               else
                 (let uu____14718 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14718 c)
                in
             let inversion_axioms tapp vars =
               let uu____14736 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14744 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14744 FStar_Option.isNone))
                  in
               if uu____14736
               then []
               else
                 (let uu____14779 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14779 with
                  | (xxsym,xx) ->
                      let uu____14792 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14831  ->
                                fun l  ->
                                  match uu____14831 with
                                  | (out,decls) ->
                                      let uu____14851 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14851 with
                                       | (uu____14862,data_t) ->
                                           let uu____14864 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14864 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14908 =
                                                    let uu____14909 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14909.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14908 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14912,indices)
                                                      -> indices
                                                  | uu____14938 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14968  ->
                                                            match uu____14968
                                                            with
                                                            | (x,uu____14976)
                                                                ->
                                                                let uu____14981
                                                                  =
                                                                  let uu____14982
                                                                    =
                                                                    let uu____14990
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14990,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14982
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14981)
                                                       env)
                                                   in
                                                let uu____14995 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14995 with
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
                                                                  let uu____15030
                                                                    =
                                                                    let uu____15035
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____15035,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____15030)
                                                             vars indices1
                                                         else []  in
                                                       let uu____15038 =
                                                         let uu____15039 =
                                                           let uu____15044 =
                                                             let uu____15045
                                                               =
                                                               let uu____15050
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____15051
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____15050,
                                                                 uu____15051)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____15045
                                                              in
                                                           (out, uu____15044)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____15039
                                                          in
                                                       (uu____15038,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14792 with
                       | (data_ax,decls) ->
                           let uu____15066 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____15066 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu____15083 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____15083 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____15090 =
                                    let uu____15098 =
                                      let uu____15099 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15100 =
                                        let uu____15111 =
                                          let uu____15112 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15114 =
                                            let uu____15117 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15117 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15112 uu____15114
                                           in
                                        let uu____15119 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15111,
                                          uu____15119)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15099 uu____15100
                                       in
                                    let uu____15128 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____15098,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15128)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____15090
                                   in
                                let uu____15134 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15134)))
                in
             let uu____15141 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15163 ->
                     let uu____15164 =
                       let uu____15171 =
                         let uu____15172 =
                           let uu____15187 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15187)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15172  in
                       FStar_Syntax_Syntax.mk uu____15171  in
                     uu____15164 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15141 with
             | (formals,res) ->
                 let uu____15227 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15227 with
                  | (vars,guards,env',binder_decls,uu____15252) ->
                      let arity = FStar_List.length vars  in
                      let uu____15266 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15266 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15292 =
                               let uu____15300 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15300)  in
                             FStar_SMTEncoding_Util.mkApp uu____15292  in
                           let uu____15306 =
                             let tname_decl =
                               let uu____15316 =
                                 let uu____15317 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15336 =
                                             let uu____15338 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15338
                                              in
                                           let uu____15340 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15336, uu____15340, false)))
                                    in
                                 let uu____15344 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15317,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15344, false)
                                  in
                               constructor_or_logic_type_decl uu____15316  in
                             let uu____15352 =
                               match vars with
                               | [] ->
                                   let uu____15365 =
                                     let uu____15366 =
                                       let uu____15369 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _15375  ->
                                            FStar_Pervasives_Native.Some
                                              _15375) uu____15369
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15366
                                      in
                                   ([], uu____15365)
                               | uu____15378 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15388 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15388
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15404 =
                                       let uu____15412 =
                                         let uu____15413 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15414 =
                                           let uu____15430 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15430)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15413 uu____15414
                                          in
                                       (uu____15412,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15404
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15352 with
                             | (tok_decls,env2) ->
                                 let uu____15457 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15457
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15306 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15485 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15485 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____15507 =
                                            let uu____15508 =
                                              let uu____15516 =
                                                let uu____15517 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15517
                                                 in
                                              (uu____15516,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15508
                                             in
                                          [uu____15507]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15527 =
                                          FStar_List.map
                                            (fun uu____15531  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15527 true
                                         in
                                      let uu____15533 =
                                        let uu____15536 =
                                          let uu____15539 =
                                            let uu____15542 =
                                              let uu____15543 =
                                                let uu____15551 =
                                                  let uu____15552 =
                                                    let uu____15557 =
                                                      let uu____15558 =
                                                        let uu____15569 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15569)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15558
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15557)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15552
                                                   in
                                                (uu____15551,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15543
                                               in
                                            [uu____15542]  in
                                          FStar_List.append karr uu____15539
                                           in
                                        FStar_All.pipe_right uu____15536
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15533
                                   in
                                let aux =
                                  let uu____15588 =
                                    let uu____15591 =
                                      inversion_axioms tapp vars  in
                                    let uu____15594 =
                                      let uu____15597 =
                                        let uu____15600 =
                                          let uu____15601 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15601 env2 tapp
                                            vars
                                           in
                                        [uu____15600]  in
                                      FStar_All.pipe_right uu____15597
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15591 uu____15594
                                     in
                                  FStar_List.append kindingAx uu____15588  in
                                let g =
                                  let uu____15609 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15609
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15617,uu____15618,uu____15619,uu____15620,uu____15621)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15629,t,uu____15631,n_tps,uu____15633) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15644 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15644 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15692 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15692 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15716 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15716 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15736 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15736 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15815 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15815,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15822 =
                                   let uu____15823 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15823, true)
                                    in
                                 let uu____15831 =
                                   let uu____15838 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15838
                                    in
                                 FStar_All.pipe_right uu____15822 uu____15831
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
                               let uu____15850 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15850 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15862::uu____15863 ->
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
                                            let uu____15912 =
                                              let uu____15913 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15913]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15912
                                             in
                                          let uu____15939 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15940 =
                                            let uu____15951 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15951)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15939 uu____15940
                                      | uu____15978 -> tok_typing  in
                                    let uu____15989 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15989 with
                                     | (vars',guards',env'',decls_formals,uu____16014)
                                         ->
                                         let uu____16027 =
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
                                         (match uu____16027 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____16057 ->
                                                    let uu____16066 =
                                                      let uu____16067 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16067
                                                       in
                                                    [uu____16066]
                                                 in
                                              let encode_elim uu____16083 =
                                                let uu____16084 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16084 with
                                                | (head1,args) ->
                                                    let uu____16135 =
                                                      let uu____16136 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____16136.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16135 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16148;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16149;_},uu____16150)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16156 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16156
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
                                                                  | uu____16219
                                                                    ->
                                                                    let uu____16220
                                                                    =
                                                                    let uu____16226
                                                                    =
                                                                    let uu____16228
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16228
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16226)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16220
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16251
                                                                    =
                                                                    let uu____16253
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16253
                                                                     in
                                                                    if
                                                                    uu____16251
                                                                    then
                                                                    let uu____16275
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16275]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16278
                                                                =
                                                                let uu____16292
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16349
                                                                     ->
                                                                    fun
                                                                    uu____16350
                                                                     ->
                                                                    match 
                                                                    (uu____16349,
                                                                    uu____16350)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16461
                                                                    =
                                                                    let uu____16469
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16469
                                                                     in
                                                                    (match uu____16461
                                                                    with
                                                                    | 
                                                                    (uu____16483,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16494
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16494
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16499
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16499
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu____16292
                                                                 in
                                                              (match uu____16278
                                                               with
                                                               | (uu____16520,arg_vars,elim_eqns_or_guards,uu____16523)
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
                                                                    let uu____16550
                                                                    =
                                                                    let uu____16558
                                                                    =
                                                                    let uu____16559
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16560
                                                                    =
                                                                    let uu____16571
                                                                    =
                                                                    let uu____16572
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16572
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16574
                                                                    =
                                                                    let uu____16575
                                                                    =
                                                                    let uu____16580
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16580)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16575
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16571,
                                                                    uu____16574)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16559
                                                                    uu____16560
                                                                     in
                                                                    (uu____16558,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16550
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16595
                                                                    =
                                                                    let uu____16596
                                                                    =
                                                                    let uu____16602
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16602,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16596
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16595
                                                                     in
                                                                    let uu____16605
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16605
                                                                    then
                                                                    let x =
                                                                    let uu____16609
                                                                    =
                                                                    let uu____16615
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16615,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16609
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16620
                                                                    =
                                                                    let uu____16628
                                                                    =
                                                                    let uu____16629
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16630
                                                                    =
                                                                    let uu____16641
                                                                    =
                                                                    let uu____16646
                                                                    =
                                                                    let uu____16649
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16649]
                                                                     in
                                                                    [uu____16646]
                                                                     in
                                                                    let uu____16654
                                                                    =
                                                                    let uu____16655
                                                                    =
                                                                    let uu____16660
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16660,
                                                                    uu____16662)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16655
                                                                     in
                                                                    (uu____16641,
                                                                    [x],
                                                                    uu____16654)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16629
                                                                    uu____16630
                                                                     in
                                                                    let uu____16683
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16628,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16683)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16620
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16694
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
                                                                    (let uu____16717
                                                                    =
                                                                    let uu____16718
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16718
                                                                    dapp1  in
                                                                    [uu____16717])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16694
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16725
                                                                    =
                                                                    let uu____16733
                                                                    =
                                                                    let uu____16734
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16735
                                                                    =
                                                                    let uu____16746
                                                                    =
                                                                    let uu____16747
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16747
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16749
                                                                    =
                                                                    let uu____16750
                                                                    =
                                                                    let uu____16755
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16755)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16750
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16746,
                                                                    uu____16749)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16734
                                                                    uu____16735
                                                                     in
                                                                    (uu____16733,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16725)
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
                                                         let uu____16774 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16774
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
                                                                  | uu____16837
                                                                    ->
                                                                    let uu____16838
                                                                    =
                                                                    let uu____16844
                                                                    =
                                                                    let uu____16846
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16846
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16844)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16838
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16869
                                                                    =
                                                                    let uu____16871
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16871
                                                                     in
                                                                    if
                                                                    uu____16869
                                                                    then
                                                                    let uu____16893
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16893]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16896
                                                                =
                                                                let uu____16910
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16967
                                                                     ->
                                                                    fun
                                                                    uu____16968
                                                                     ->
                                                                    match 
                                                                    (uu____16967,
                                                                    uu____16968)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____17079
                                                                    =
                                                                    let uu____17087
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____17087
                                                                     in
                                                                    (match uu____17079
                                                                    with
                                                                    | 
                                                                    (uu____17101,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17112
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17112
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17117
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17117
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu____16910
                                                                 in
                                                              (match uu____16896
                                                               with
                                                               | (uu____17138,arg_vars,elim_eqns_or_guards,uu____17141)
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
                                                                    let uu____17168
                                                                    =
                                                                    let uu____17176
                                                                    =
                                                                    let uu____17177
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17178
                                                                    =
                                                                    let uu____17189
                                                                    =
                                                                    let uu____17190
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17190
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17192
                                                                    =
                                                                    let uu____17193
                                                                    =
                                                                    let uu____17198
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17198)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17193
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17189,
                                                                    uu____17192)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17177
                                                                    uu____17178
                                                                     in
                                                                    (uu____17176,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17168
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____17213
                                                                    =
                                                                    let uu____17214
                                                                    =
                                                                    let uu____17220
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17220,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17214
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17213
                                                                     in
                                                                    let uu____17223
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____17223
                                                                    then
                                                                    let x =
                                                                    let uu____17227
                                                                    =
                                                                    let uu____17233
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____17233,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17227
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____17238
                                                                    =
                                                                    let uu____17246
                                                                    =
                                                                    let uu____17247
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17248
                                                                    =
                                                                    let uu____17259
                                                                    =
                                                                    let uu____17264
                                                                    =
                                                                    let uu____17267
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____17267]
                                                                     in
                                                                    [uu____17264]
                                                                     in
                                                                    let uu____17272
                                                                    =
                                                                    let uu____17273
                                                                    =
                                                                    let uu____17278
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____17280
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____17278,
                                                                    uu____17280)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17273
                                                                     in
                                                                    (uu____17259,
                                                                    [x],
                                                                    uu____17272)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17247
                                                                    uu____17248
                                                                     in
                                                                    let uu____17301
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____17246,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____17301)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17238
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____17312
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
                                                                    (let uu____17335
                                                                    =
                                                                    let uu____17336
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____17336
                                                                    dapp1  in
                                                                    [uu____17335])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17312
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17343
                                                                    =
                                                                    let uu____17351
                                                                    =
                                                                    let uu____17352
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17353
                                                                    =
                                                                    let uu____17364
                                                                    =
                                                                    let uu____17365
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17365
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17367
                                                                    =
                                                                    let uu____17368
                                                                    =
                                                                    let uu____17373
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17373)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17368
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17364,
                                                                    uu____17367)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17352
                                                                    uu____17353
                                                                     in
                                                                    (uu____17351,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17343)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17390 ->
                                                         ((let uu____17392 =
                                                             let uu____17398
                                                               =
                                                               let uu____17400
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17402
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17400
                                                                 uu____17402
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17398)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17392);
                                                          ([], [])))
                                                 in
                                              let uu____17410 =
                                                encode_elim ()  in
                                              (match uu____17410 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17436 =
                                                       let uu____17439 =
                                                         let uu____17442 =
                                                           let uu____17445 =
                                                             let uu____17448
                                                               =
                                                               let uu____17451
                                                                 =
                                                                 let uu____17454
                                                                   =
                                                                   let uu____17455
                                                                    =
                                                                    let uu____17467
                                                                    =
                                                                    let uu____17468
                                                                    =
                                                                    let uu____17470
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17470
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17468
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17467)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17455
                                                                    in
                                                                 [uu____17454]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17451
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17448
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17481 =
                                                             let uu____17484
                                                               =
                                                               let uu____17487
                                                                 =
                                                                 let uu____17490
                                                                   =
                                                                   let uu____17493
                                                                    =
                                                                    let uu____17496
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17501
                                                                    =
                                                                    let uu____17504
                                                                    =
                                                                    let uu____17505
                                                                    =
                                                                    let uu____17513
                                                                    =
                                                                    let uu____17514
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17515
                                                                    =
                                                                    let uu____17526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17526)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17514
                                                                    uu____17515
                                                                     in
                                                                    (uu____17513,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17505
                                                                     in
                                                                    let uu____17539
                                                                    =
                                                                    let uu____17542
                                                                    =
                                                                    let uu____17543
                                                                    =
                                                                    let uu____17551
                                                                    =
                                                                    let uu____17552
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17553
                                                                    =
                                                                    let uu____17564
                                                                    =
                                                                    let uu____17565
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17565
                                                                    vars'  in
                                                                    let uu____17567
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17564,
                                                                    uu____17567)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17552
                                                                    uu____17553
                                                                     in
                                                                    (uu____17551,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17543
                                                                     in
                                                                    [uu____17542]
                                                                     in
                                                                    uu____17504
                                                                    ::
                                                                    uu____17539
                                                                     in
                                                                    uu____17496
                                                                    ::
                                                                    uu____17501
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17493
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17490
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17487
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17484
                                                              in
                                                           FStar_List.append
                                                             uu____17445
                                                             uu____17481
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17442
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17439
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17436
                                                      in
                                                   let uu____17584 =
                                                     let uu____17585 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17585 g
                                                      in
                                                   (uu____17584, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17619  ->
              fun se  ->
                match uu____17619 with
                | (g,env1) ->
                    let uu____17639 = encode_sigelt env1 se  in
                    (match uu____17639 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17707 =
        match uu____17707 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17744 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17752 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17752
                   then
                     let uu____17757 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17759 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17761 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17757 uu____17759 uu____17761
                   else ());
                  (let uu____17766 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17766 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17784 =
                         let uu____17792 =
                           let uu____17794 =
                             let uu____17796 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17796
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17794  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17792
                          in
                       (match uu____17784 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17816 = FStar_Options.log_queries ()
                                 in
                              if uu____17816
                              then
                                let uu____17819 =
                                  let uu____17821 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17823 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17825 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17821 uu____17823 uu____17825
                                   in
                                FStar_Pervasives_Native.Some uu____17819
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17841 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17851 =
                                let uu____17854 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17854  in
                              FStar_List.append uu____17841 uu____17851  in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17866,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17886 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17886 with
                  | (g,env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env')))
         in
      let uu____17907 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env)
         in
      match uu____17907 with | (uu____17934,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17987  ->
              match uu____17987 with
              | (l,uu____17996,uu____17997) ->
                  let uu____18000 =
                    let uu____18012 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____18012, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____18000))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____18045  ->
              match uu____18045 with
              | (l,uu____18056,uu____18057) ->
                  let uu____18060 =
                    let uu____18061 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _18064  -> FStar_SMTEncoding_Term.Echo _18064)
                      uu____18061
                     in
                  let uu____18065 =
                    let uu____18068 =
                      let uu____18069 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____18069  in
                    [uu____18068]  in
                  uu____18060 :: uu____18065))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____18087 =
      let uu____18090 =
        let uu____18091 = FStar_Util.psmap_empty ()  in
        let uu____18106 =
          let uu____18115 = FStar_Util.psmap_empty ()  in (uu____18115, [])
           in
        let uu____18122 =
          let uu____18124 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____18124 FStar_Ident.string_of_lid  in
        let uu____18126 = FStar_Util.smap_create (Prims.of_int (100))  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____18091;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18106;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18122;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18126
        }  in
      [uu____18090]  in
    FStar_ST.op_Colon_Equals last_env uu____18087
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____18170 = FStar_ST.op_Bang last_env  in
      match uu____18170 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18198 ->
          let uu___1568_18201 = e  in
          let uu____18202 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1568_18201.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1568_18201.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1568_18201.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1568_18201.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1568_18201.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1568_18201.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1568_18201.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18202;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1568_18201.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1568_18201.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18210 = FStar_ST.op_Bang last_env  in
    match uu____18210 with
    | [] -> failwith "Empty env stack"
    | uu____18237::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____18269  ->
    let uu____18270 = FStar_ST.op_Bang last_env  in
    match uu____18270 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____18330  ->
    let uu____18331 = FStar_ST.op_Bang last_env  in
    match uu____18331 with
    | [] -> failwith "Popping an empty stack"
    | uu____18358::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18395  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18448  ->
         let uu____18449 = snapshot_env ()  in
         match uu____18449 with
         | (env_depth,()) ->
             let uu____18471 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18471 with
              | (varops_depth,()) ->
                  let uu____18493 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18493 with
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
        (fun uu____18551  ->
           let uu____18552 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18552 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18647 = snapshot msg  in () 
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
        | (uu____18693::uu____18694,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1629_18702 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1629_18702.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1629_18702.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1629_18702.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18703 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1635_18730 = elt  in
        let uu____18731 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1635_18730.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1635_18730.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18731;
          FStar_SMTEncoding_Term.a_names =
            (uu___1635_18730.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18751 =
        let uu____18754 =
          let uu____18755 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18755  in
        let uu____18756 = open_fact_db_tags env  in uu____18754 ::
          uu____18756
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18751
  
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
      let uu____18783 = encode_sigelt env se  in
      match uu____18783 with
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
                (let uu____18829 =
                   let uu____18832 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18832
                    in
                 match uu____18829 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18847 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18847
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18877 = FStar_Options.log_queries ()  in
        if uu____18877
        then
          let uu____18882 =
            let uu____18883 =
              let uu____18885 =
                let uu____18887 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18887 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18885  in
            FStar_SMTEncoding_Term.Caption uu____18883  in
          uu____18882 :: decls
        else decls  in
      (let uu____18906 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18906
       then
         let uu____18909 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18909
       else ());
      (let env =
         let uu____18915 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18915 tcenv  in
       let uu____18916 = encode_top_level_facts env se  in
       match uu____18916 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18930 =
               let uu____18933 =
                 let uu____18936 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18936
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18933  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18930)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18969 = FStar_Options.log_queries ()  in
          if uu____18969
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1673_18989 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1673_18989.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1673_18989.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1673_18989.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1673_18989.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1673_18989.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1673_18989.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1673_18989.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1673_18989.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1673_18989.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1673_18989.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18994 =
             let uu____18997 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18997
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18994  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____19017 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____19017
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
          (let uu____19041 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____19041
           then
             let uu____19044 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____19044
           else ());
          (let env =
             let uu____19052 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____19052
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____19091  ->
                     fun se  ->
                       match uu____19091 with
                       | (g,env2) ->
                           let uu____19111 = encode_top_level_facts env2 se
                              in
                           (match uu____19111 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____19134 =
             encode_signature
               (let uu___1696_19143 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1696_19143.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1696_19143.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1696_19143.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1696_19143.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1696_19143.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1696_19143.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1696_19143.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1696_19143.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1696_19143.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1696_19143.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____19134 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19159 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19159
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____19165 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____19165))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun tcmod  ->
      fun uu____19193  ->
        match uu____19193 with
        | (decls,fvbs) ->
            let uu____19206 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
            if uu____19206
            then ()
            else
              (let name =
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module")
                   (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               (let uu____19221 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____19221
                then
                  let uu____19224 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int
                     in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19224
                else ());
               (let env =
                  let uu____19232 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv  in
                  FStar_All.pipe_right uu____19232
                    FStar_SMTEncoding_Env.reset_current_module_fvbs
                   in
                let env1 =
                  let uu____19234 = FStar_All.pipe_right fvbs FStar_List.rev
                     in
                  FStar_All.pipe_right uu____19234
                    (FStar_List.fold_left
                       (fun env1  ->
                          fun fvb  ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env)
                   in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19248 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19248
                 then
                   FStar_Util.print1
                     "Done encoding externals from cache for %s\n" name
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
        (let uu____19310 =
           let uu____19312 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____19312.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19310);
        (let env =
           let uu____19314 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19314 tcenv  in
         let uu____19315 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19354 = aux rest  in
                 (match uu____19354 with
                  | (out,rest1) ->
                      let t =
                        let uu____19382 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19382 with
                        | FStar_Pervasives_Native.Some uu____19385 ->
                            let uu____19386 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19386
                              x.FStar_Syntax_Syntax.sort
                        | uu____19387 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19391 =
                        let uu____19394 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1739_19397 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1739_19397.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1739_19397.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19394 :: out  in
                      (uu____19391, rest1))
             | uu____19402 -> ([], bindings)  in
           let uu____19409 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19409 with
           | (closing,bindings) ->
               let uu____19436 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19436, bindings)
            in
         match uu____19315 with
         | (q1,bindings) ->
             let uu____19467 = encode_env_bindings env bindings  in
             (match uu____19467 with
              | (env_decls,env1) ->
                  ((let uu____19489 =
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
                    if uu____19489
                    then
                      let uu____19496 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____19496
                    else ());
                   (let uu____19501 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____19501 with
                    | (phi,qdecls) ->
                        let uu____19522 =
                          let uu____19527 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19527 phi
                           in
                        (match uu____19522 with
                         | (labels,phi1) ->
                             let uu____19544 = encode_labels labels  in
                             (match uu____19544 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19580 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19580
                                    then
                                      let uu____19585 =
                                        let uu____19586 =
                                          let uu____19588 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula: "
                                            uu____19588
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19586
                                         in
                                      [uu____19585]
                                    else []  in
                                  let query_prelude =
                                    let uu____19596 =
                                      let uu____19597 =
                                        let uu____19598 =
                                          let uu____19601 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19608 =
                                            let uu____19611 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19611
                                             in
                                          FStar_List.append uu____19601
                                            uu____19608
                                           in
                                        FStar_List.append env_decls
                                          uu____19598
                                         in
                                      FStar_All.pipe_right uu____19597
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19596
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19621 =
                                      let uu____19629 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19630 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19629,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19630)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19621
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
  