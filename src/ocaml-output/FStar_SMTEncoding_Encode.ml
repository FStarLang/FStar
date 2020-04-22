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
      let uu____15 =
        let uu____19 =
          let uu____21 =
            FStar_TypeChecker_Env.current_module
              env.FStar_SMTEncoding_Env.tcenv
             in
          FStar_Ident.string_of_lid uu____21  in
        FStar_Pervasives_Native.Some uu____19  in
      FStar_Profiling.profile
        (fun uu____24  ->
           FStar_TypeChecker_Normalize.normalize steps
             env.FStar_SMTEncoding_Env.tcenv t) uu____15
        "FStar.TypeChecker.SMTEncoding.Encode.norm_before_encoding"
  
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        let uu____42 =
          let uu____46 =
            let uu____48 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____48  in
          FStar_Pervasives_Native.Some uu____46  in
        FStar_Profiling.profile
          (fun uu____51  -> FStar_TypeChecker_Normalize.normalize steps env t)
          uu____42 "FStar.TypeChecker.SMTEncoding.Encode.norm"
  
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
  = fun projectee  -> match projectee with | { mk; is;_} -> mk 
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  -> match projectee with | { mk; is;_} -> is 
let (prims : prims_t) =
  let module_name = "Prims"  in
  let uu____192 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____192 with
  | (asym,a) ->
      let uu____203 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____203 with
       | (xsym,x) ->
           let uu____214 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____214 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____292 =
                      let uu____304 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____304, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____292  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____324 =
                      let uu____332 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____332)  in
                    FStar_SMTEncoding_Util.mkApp uu____324  in
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
                      let uu____427 =
                        let uu____435 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1  in
                        (uu____435, FStar_Pervasives_Native.None, axiom_name)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____427  in
                    let uu____438 =
                      FStar_List.fold_left
                        (fun uu____492  ->
                           fun var  ->
                             match uu____492 with
                             | (axioms,app,vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var]
                                    in
                                 let vars2 = FStar_List.append vars1 [var]
                                    in
                                 let axiom_name1 =
                                   let uu____619 =
                                     let uu____621 =
                                       let uu____623 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length
                                          in
                                       Prims.string_of_int uu____623  in
                                     Prims.op_Hat "." uu____621  in
                                   Prims.op_Hat axiom_name uu____619  in
                                 let uu____645 =
                                   let uu____648 =
                                     let uu____651 =
                                       let uu____652 =
                                         let uu____660 =
                                           let uu____661 =
                                             let uu____672 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1
                                                in
                                             ([[app1]], vars2, uu____672)  in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____661
                                            in
                                         (uu____660,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1)
                                          in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____652
                                        in
                                     [uu____651]  in
                                   FStar_List.append axioms uu____648  in
                                 (uu____645, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one
                       in
                    match uu____438 with
                    | (axioms,uu____718,uu____719) -> axioms  in
                  let uu____744 =
                    let uu____747 =
                      let uu____750 =
                        let uu____753 =
                          let uu____756 =
                            let uu____757 =
                              let uu____765 =
                                let uu____766 =
                                  let uu____777 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, uu____777)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____766
                                 in
                              (uu____765, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____757  in
                          [uu____756]  in
                        xtok_decl :: uu____753  in
                      xname_decl :: uu____750  in
                    let uu____789 =
                      let uu____792 =
                        let uu____795 =
                          let uu____796 =
                            let uu____804 =
                              let uu____805 =
                                let uu____816 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp)
                                   in
                                ([[xtok_app]], vars, uu____816)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____805
                               in
                            (uu____804,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____796  in
                        [uu____795]  in
                      FStar_List.append tot_fun_axioms uu____792  in
                    FStar_List.append uu____747 uu____789  in
                  (xtok1, (FStar_List.length vars), uu____744)  in
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
                let prims =
                  let uu____986 =
                    let uu____1007 =
                      let uu____1026 =
                        let uu____1027 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____1027
                         in
                      quant axy uu____1026  in
                    (FStar_Parser_Const.op_Eq, uu____1007)  in
                  let uu____1044 =
                    let uu____1067 =
                      let uu____1088 =
                        let uu____1107 =
                          let uu____1108 =
                            let uu____1109 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____1109  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1108
                           in
                        quant axy uu____1107  in
                      (FStar_Parser_Const.op_notEq, uu____1088)  in
                    let uu____1126 =
                      let uu____1149 =
                        let uu____1170 =
                          let uu____1189 =
                            let uu____1190 =
                              let uu____1191 =
                                let uu____1196 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____1197 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____1196, uu____1197)  in
                              FStar_SMTEncoding_Util.mkAnd uu____1191  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1190
                             in
                          quant xy uu____1189  in
                        (FStar_Parser_Const.op_And, uu____1170)  in
                      let uu____1214 =
                        let uu____1237 =
                          let uu____1258 =
                            let uu____1277 =
                              let uu____1278 =
                                let uu____1279 =
                                  let uu____1284 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____1285 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____1284, uu____1285)  in
                                FStar_SMTEncoding_Util.mkOr uu____1279  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1278
                               in
                            quant xy uu____1277  in
                          (FStar_Parser_Const.op_Or, uu____1258)  in
                        let uu____1302 =
                          let uu____1325 =
                            let uu____1346 =
                              let uu____1365 =
                                let uu____1366 =
                                  let uu____1367 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____1367  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1366
                                 in
                              quant qx uu____1365  in
                            (FStar_Parser_Const.op_Negation, uu____1346)  in
                          let uu____1384 =
                            let uu____1407 =
                              let uu____1428 =
                                let uu____1447 =
                                  let uu____1448 =
                                    let uu____1449 =
                                      let uu____1454 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1455 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1454, uu____1455)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1449
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1448
                                   in
                                quant xy uu____1447  in
                              (FStar_Parser_Const.op_LT, uu____1428)  in
                            let uu____1472 =
                              let uu____1495 =
                                let uu____1516 =
                                  let uu____1535 =
                                    let uu____1536 =
                                      let uu____1537 =
                                        let uu____1542 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1543 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1542, uu____1543)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1537
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1536
                                     in
                                  quant xy uu____1535  in
                                (FStar_Parser_Const.op_LTE, uu____1516)  in
                              let uu____1560 =
                                let uu____1583 =
                                  let uu____1604 =
                                    let uu____1623 =
                                      let uu____1624 =
                                        let uu____1625 =
                                          let uu____1630 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1631 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1630, uu____1631)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1625
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1624
                                       in
                                    quant xy uu____1623  in
                                  (FStar_Parser_Const.op_GT, uu____1604)  in
                                let uu____1648 =
                                  let uu____1671 =
                                    let uu____1692 =
                                      let uu____1711 =
                                        let uu____1712 =
                                          let uu____1713 =
                                            let uu____1718 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1719 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1718, uu____1719)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1713
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1712
                                         in
                                      quant xy uu____1711  in
                                    (FStar_Parser_Const.op_GTE, uu____1692)
                                     in
                                  let uu____1736 =
                                    let uu____1759 =
                                      let uu____1780 =
                                        let uu____1799 =
                                          let uu____1800 =
                                            let uu____1801 =
                                              let uu____1806 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1807 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1806, uu____1807)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1801
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1800
                                           in
                                        quant xy uu____1799  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1780)
                                       in
                                    let uu____1824 =
                                      let uu____1847 =
                                        let uu____1868 =
                                          let uu____1887 =
                                            let uu____1888 =
                                              let uu____1889 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1889
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1888
                                             in
                                          quant qx uu____1887  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1868)
                                         in
                                      let uu____1906 =
                                        let uu____1929 =
                                          let uu____1950 =
                                            let uu____1969 =
                                              let uu____1970 =
                                                let uu____1971 =
                                                  let uu____1976 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1977 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1976, uu____1977)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1971
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1970
                                               in
                                            quant xy uu____1969  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1950)
                                           in
                                        let uu____1994 =
                                          let uu____2017 =
                                            let uu____2038 =
                                              let uu____2057 =
                                                let uu____2058 =
                                                  let uu____2059 =
                                                    let uu____2064 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____2065 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____2064, uu____2065)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2059
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2058
                                                 in
                                              quant xy uu____2057  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2038)
                                             in
                                          let uu____2082 =
                                            let uu____2105 =
                                              let uu____2126 =
                                                let uu____2145 =
                                                  let uu____2146 =
                                                    let uu____2147 =
                                                      let uu____2152 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____2153 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____2152,
                                                        uu____2153)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2147
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2146
                                                   in
                                                quant xy uu____2145  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2126)
                                               in
                                            let uu____2170 =
                                              let uu____2193 =
                                                let uu____2214 =
                                                  let uu____2233 =
                                                    let uu____2234 =
                                                      let uu____2235 =
                                                        let uu____2240 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____2241 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____2240,
                                                          uu____2241)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2235
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2234
                                                     in
                                                  quant xy uu____2233  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2214)
                                                 in
                                              let uu____2258 =
                                                let uu____2281 =
                                                  let uu____2302 =
                                                    let uu____2321 =
                                                      let uu____2322 =
                                                        let uu____2323 =
                                                          let uu____2328 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____2329 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____2328,
                                                            uu____2329)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2323
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2322
                                                       in
                                                    quant xy uu____2321  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2302)
                                                   in
                                                let uu____2346 =
                                                  let uu____2369 =
                                                    let uu____2390 =
                                                      let uu____2409 =
                                                        let uu____2410 =
                                                          let uu____2411 =
                                                            let uu____2416 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____2417 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____2416,
                                                              uu____2417)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2411
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2410
                                                         in
                                                      quant xy uu____2409  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2390)
                                                     in
                                                  let uu____2434 =
                                                    let uu____2457 =
                                                      let uu____2478 =
                                                        let uu____2497 =
                                                          let uu____2498 =
                                                            let uu____2499 =
                                                              let uu____2504
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2505
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2504,
                                                                uu____2505)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2499
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2498
                                                           in
                                                        quant xy uu____2497
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2478)
                                                       in
                                                    let uu____2522 =
                                                      let uu____2545 =
                                                        let uu____2566 =
                                                          let uu____2585 =
                                                            let uu____2586 =
                                                              let uu____2587
                                                                =
                                                                let uu____2592
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2593
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2592,
                                                                  uu____2593)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2587
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2586
                                                             in
                                                          quant xy uu____2585
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2566)
                                                         in
                                                      let uu____2610 =
                                                        let uu____2633 =
                                                          let uu____2654 =
                                                            let uu____2673 =
                                                              let uu____2674
                                                                =
                                                                let uu____2675
                                                                  =
                                                                  let uu____2680
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2681
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2680,
                                                                    uu____2681)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2675
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2674
                                                               in
                                                            quant xy
                                                              uu____2673
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2654)
                                                           in
                                                        let uu____2698 =
                                                          let uu____2721 =
                                                            let uu____2742 =
                                                              let uu____2761
                                                                =
                                                                let uu____2762
                                                                  =
                                                                  let uu____2763
                                                                    =
                                                                    let uu____2768
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2769
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2768,
                                                                    uu____2769)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2763
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2762
                                                                 in
                                                              quant xy
                                                                uu____2761
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2742)
                                                             in
                                                          let uu____2786 =
                                                            let uu____2809 =
                                                              let uu____2830
                                                                =
                                                                let uu____2849
                                                                  =
                                                                  let uu____2850
                                                                    =
                                                                    let uu____2851
                                                                    =
                                                                    let uu____2856
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2857
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2856,
                                                                    uu____2857)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2851
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2850
                                                                   in
                                                                quant xy
                                                                  uu____2849
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2830)
                                                               in
                                                            let uu____2874 =
                                                              let uu____2897
                                                                =
                                                                let uu____2918
                                                                  =
                                                                  let uu____2937
                                                                    =
                                                                    let uu____2938
                                                                    =
                                                                    let uu____2939
                                                                    =
                                                                    let uu____2944
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2945
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2944,
                                                                    uu____2945)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2939
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2938
                                                                     in
                                                                  quant xy
                                                                    uu____2937
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2918)
                                                                 in
                                                              let uu____2962
                                                                =
                                                                let uu____2985
                                                                  =
                                                                  let uu____3006
                                                                    =
                                                                    let uu____3025
                                                                    =
                                                                    let uu____3026
                                                                    =
                                                                    let uu____3027
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____3027
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____3026
                                                                     in
                                                                    quant qx
                                                                    uu____3025
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____3006)
                                                                   in
                                                                [uu____2985]
                                                                 in
                                                              uu____2897 ::
                                                                uu____2962
                                                               in
                                                            uu____2809 ::
                                                              uu____2874
                                                             in
                                                          uu____2721 ::
                                                            uu____2786
                                                           in
                                                        uu____2633 ::
                                                          uu____2698
                                                         in
                                                      uu____2545 ::
                                                        uu____2610
                                                       in
                                                    uu____2457 :: uu____2522
                                                     in
                                                  uu____2369 :: uu____2434
                                                   in
                                                uu____2281 :: uu____2346  in
                                              uu____2193 :: uu____2258  in
                                            uu____2105 :: uu____2170  in
                                          uu____2017 :: uu____2082  in
                                        uu____1929 :: uu____1994  in
                                      uu____1847 :: uu____1906  in
                                    uu____1759 :: uu____1824  in
                                  uu____1671 :: uu____1736  in
                                uu____1583 :: uu____1648  in
                              uu____1495 :: uu____1560  in
                            uu____1407 :: uu____1472  in
                          uu____1325 :: uu____1384  in
                        uu____1237 :: uu____1302  in
                      uu____1149 :: uu____1214  in
                    uu____1067 :: uu____1126  in
                  uu____986 :: uu____1044  in
                let mk l v =
                  let uu____3566 =
                    let uu____3578 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____3668  ->
                              match uu____3668 with
                              | (l',uu____3689) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3578
                      (FStar_Option.map
                         (fun uu____3788  ->
                            match uu____3788 with
                            | (uu____3816,b) ->
                                let uu____3850 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3850 v))
                     in
                  FStar_All.pipe_right uu____3566 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____3933  ->
                          match uu____3933 with
                          | (l',uu____3954) -> FStar_Ident.lid_equals l l'))
                   in
                { mk; is }))
  
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
          let uu____4028 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____4028 with
          | (xxsym,xx) ->
              let uu____4039 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____4039 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____4055 =
                     let uu____4063 =
                       let uu____4064 =
                         let uu____4075 =
                           let uu____4076 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____4086 =
                             let uu____4097 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____4097 :: vars  in
                           uu____4076 :: uu____4086  in
                         let uu____4123 =
                           let uu____4124 =
                             let uu____4129 =
                               let uu____4130 =
                                 let uu____4135 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____4135)  in
                               FStar_SMTEncoding_Util.mkEq uu____4130  in
                             (xx_has_type, uu____4129)  in
                           FStar_SMTEncoding_Util.mkImp uu____4124  in
                         ([[xx_has_type]], uu____4075, uu____4123)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____4064  in
                     let uu____4148 =
                       let uu____4150 =
                         let uu____4152 =
                           let uu____4154 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____4154  in
                         Prims.op_Hat module_name uu____4152  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____4150
                        in
                     (uu____4063, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____4148)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____4055)
  
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
  let mkForall_fuel env =
    let uu____4210 =
      let uu____4212 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____4212  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4210  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____4234 =
      let uu____4235 =
        let uu____4243 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____4243, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4235  in
    let uu____4248 =
      let uu____4251 =
        let uu____4252 =
          let uu____4260 =
            let uu____4261 =
              let uu____4272 =
                let uu____4273 =
                  let uu____4278 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____4278)  in
                FStar_SMTEncoding_Util.mkImp uu____4273  in
              ([[typing_pred]], [xx], uu____4272)  in
            let uu____4303 =
              let uu____4318 = FStar_TypeChecker_Env.get_range env  in
              let uu____4319 = mkForall_fuel env  in uu____4319 uu____4318
               in
            uu____4303 uu____4261  in
          (uu____4260, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4252  in
      [uu____4251]  in
    uu____4234 :: uu____4248  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4366 =
      let uu____4367 =
        let uu____4375 =
          let uu____4376 = FStar_TypeChecker_Env.get_range env  in
          let uu____4377 =
            let uu____4388 =
              let uu____4393 =
                let uu____4396 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____4396]  in
              [uu____4393]  in
            let uu____4401 =
              let uu____4402 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4402 tt  in
            (uu____4388, [bb], uu____4401)  in
          FStar_SMTEncoding_Term.mkForall uu____4376 uu____4377  in
        (uu____4375, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4367  in
    let uu____4427 =
      let uu____4430 =
        let uu____4431 =
          let uu____4439 =
            let uu____4440 =
              let uu____4451 =
                let uu____4452 =
                  let uu____4457 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4457)  in
                FStar_SMTEncoding_Util.mkImp uu____4452  in
              ([[typing_pred]], [xx], uu____4451)  in
            let uu____4484 =
              let uu____4499 = FStar_TypeChecker_Env.get_range env  in
              let uu____4500 = mkForall_fuel env  in uu____4500 uu____4499
               in
            uu____4484 uu____4440  in
          (uu____4439, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4431  in
      [uu____4430]  in
    uu____4366 :: uu____4427  in
  let mk_int env nm tt =
    let lex_t =
      let uu____4543 =
        let uu____4544 =
          let uu____4550 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4550, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4544  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4543  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4564 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4564  in
    let uu____4569 =
      let uu____4570 =
        let uu____4578 =
          let uu____4579 = FStar_TypeChecker_Env.get_range env  in
          let uu____4580 =
            let uu____4591 =
              let uu____4596 =
                let uu____4599 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4599]  in
              [uu____4596]  in
            let uu____4604 =
              let uu____4605 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4605 tt  in
            (uu____4591, [bb], uu____4604)  in
          FStar_SMTEncoding_Term.mkForall uu____4579 uu____4580  in
        (uu____4578, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4570  in
    let uu____4630 =
      let uu____4633 =
        let uu____4634 =
          let uu____4642 =
            let uu____4643 =
              let uu____4654 =
                let uu____4655 =
                  let uu____4660 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4660)  in
                FStar_SMTEncoding_Util.mkImp uu____4655  in
              ([[typing_pred]], [xx], uu____4654)  in
            let uu____4687 =
              let uu____4702 = FStar_TypeChecker_Env.get_range env  in
              let uu____4703 = mkForall_fuel env  in uu____4703 uu____4702
               in
            uu____4687 uu____4643  in
          (uu____4642, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4634  in
      let uu____4725 =
        let uu____4728 =
          let uu____4729 =
            let uu____4737 =
              let uu____4738 =
                let uu____4749 =
                  let uu____4750 =
                    let uu____4755 =
                      let uu____4756 =
                        let uu____4759 =
                          let uu____4762 =
                            let uu____4765 =
                              let uu____4766 =
                                let uu____4771 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4772 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero
                                   in
                                (uu____4771, uu____4772)  in
                              FStar_SMTEncoding_Util.mkGT uu____4766  in
                            let uu____4774 =
                              let uu____4777 =
                                let uu____4778 =
                                  let uu____4783 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4784 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero
                                     in
                                  (uu____4783, uu____4784)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4778  in
                              let uu____4786 =
                                let uu____4789 =
                                  let uu____4790 =
                                    let uu____4795 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4796 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4795, uu____4796)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4790  in
                                [uu____4789]  in
                              uu____4777 :: uu____4786  in
                            uu____4765 :: uu____4774  in
                          typing_pred_y :: uu____4762  in
                        typing_pred :: uu____4759  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4756  in
                    (uu____4755, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4750  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4749)
                 in
              let uu____4829 =
                let uu____4844 = FStar_TypeChecker_Env.get_range env  in
                let uu____4845 = mkForall_fuel env  in uu____4845 uu____4844
                 in
              uu____4829 uu____4738  in
            (uu____4737,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4729  in
        [uu____4728]  in
      uu____4633 :: uu____4725  in
    uu____4569 :: uu____4630  in
  let mk_real env nm tt =
    let lex_t =
      let uu____4888 =
        let uu____4889 =
          let uu____4895 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4895, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4889  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4888  in
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
      let uu____4911 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4911  in
    let uu____4916 =
      let uu____4917 =
        let uu____4925 =
          let uu____4926 = FStar_TypeChecker_Env.get_range env  in
          let uu____4927 =
            let uu____4938 =
              let uu____4943 =
                let uu____4946 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4946]  in
              [uu____4943]  in
            let uu____4951 =
              let uu____4952 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4952 tt  in
            (uu____4938, [bb], uu____4951)  in
          FStar_SMTEncoding_Term.mkForall uu____4926 uu____4927  in
        (uu____4925, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4917  in
    let uu____4977 =
      let uu____4980 =
        let uu____4981 =
          let uu____4989 =
            let uu____4990 =
              let uu____5001 =
                let uu____5002 =
                  let uu____5007 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____5007)  in
                FStar_SMTEncoding_Util.mkImp uu____5002  in
              ([[typing_pred]], [xx], uu____5001)  in
            let uu____5034 =
              let uu____5049 = FStar_TypeChecker_Env.get_range env  in
              let uu____5050 = mkForall_fuel env  in uu____5050 uu____5049
               in
            uu____5034 uu____4990  in
          (uu____4989, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4981  in
      let uu____5072 =
        let uu____5075 =
          let uu____5076 =
            let uu____5084 =
              let uu____5085 =
                let uu____5096 =
                  let uu____5097 =
                    let uu____5102 =
                      let uu____5103 =
                        let uu____5106 =
                          let uu____5109 =
                            let uu____5112 =
                              let uu____5113 =
                                let uu____5118 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____5119 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____5118, uu____5119)  in
                              FStar_SMTEncoding_Util.mkGT uu____5113  in
                            let uu____5121 =
                              let uu____5124 =
                                let uu____5125 =
                                  let uu____5130 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____5131 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____5130, uu____5131)  in
                                FStar_SMTEncoding_Util.mkGTE uu____5125  in
                              let uu____5133 =
                                let uu____5136 =
                                  let uu____5137 =
                                    let uu____5142 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____5143 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____5142, uu____5143)  in
                                  FStar_SMTEncoding_Util.mkLT uu____5137  in
                                [uu____5136]  in
                              uu____5124 :: uu____5133  in
                            uu____5112 :: uu____5121  in
                          typing_pred_y :: uu____5109  in
                        typing_pred :: uu____5106  in
                      FStar_SMTEncoding_Util.mk_and_l uu____5103  in
                    (uu____5102, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____5097  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____5096)
                 in
              let uu____5176 =
                let uu____5191 = FStar_TypeChecker_Env.get_range env  in
                let uu____5192 = mkForall_fuel env  in uu____5192 uu____5191
                 in
              uu____5176 uu____5085  in
            (uu____5084,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____5076  in
        [uu____5075]  in
      uu____4980 :: uu____5072  in
    uu____4916 :: uu____4977  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____5239 =
      let uu____5240 =
        let uu____5248 =
          let uu____5249 = FStar_TypeChecker_Env.get_range env  in
          let uu____5250 =
            let uu____5261 =
              let uu____5266 =
                let uu____5269 = FStar_SMTEncoding_Term.boxString b  in
                [uu____5269]  in
              [uu____5266]  in
            let uu____5274 =
              let uu____5275 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____5275 tt  in
            (uu____5261, [bb], uu____5274)  in
          FStar_SMTEncoding_Term.mkForall uu____5249 uu____5250  in
        (uu____5248, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5240  in
    let uu____5300 =
      let uu____5303 =
        let uu____5304 =
          let uu____5312 =
            let uu____5313 =
              let uu____5324 =
                let uu____5325 =
                  let uu____5330 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____5330)  in
                FStar_SMTEncoding_Util.mkImp uu____5325  in
              ([[typing_pred]], [xx], uu____5324)  in
            let uu____5357 =
              let uu____5372 = FStar_TypeChecker_Env.get_range env  in
              let uu____5373 = mkForall_fuel env  in uu____5373 uu____5372
               in
            uu____5357 uu____5313  in
          (uu____5312, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____5304  in
      [uu____5303]  in
    uu____5239 :: uu____5300  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____5420 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____5420]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5450 =
      let uu____5451 =
        let uu____5459 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5459, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5451  in
    [uu____5450]  in
  let mk_and_interp env conj uu____5482 =
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
    let uu____5511 =
      let uu____5512 =
        let uu____5520 =
          let uu____5521 = FStar_TypeChecker_Env.get_range env  in
          let uu____5522 =
            let uu____5533 =
              let uu____5534 =
                let uu____5539 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5539, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5534  in
            ([[l_and_a_b]], [aa; bb], uu____5533)  in
          FStar_SMTEncoding_Term.mkForall uu____5521 uu____5522  in
        (uu____5520, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5512  in
    [uu____5511]  in
  let mk_or_interp env disj uu____5594 =
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
    let uu____5623 =
      let uu____5624 =
        let uu____5632 =
          let uu____5633 = FStar_TypeChecker_Env.get_range env  in
          let uu____5634 =
            let uu____5645 =
              let uu____5646 =
                let uu____5651 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5651, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5646  in
            ([[l_or_a_b]], [aa; bb], uu____5645)  in
          FStar_SMTEncoding_Term.mkForall uu____5633 uu____5634  in
        (uu____5632, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5624  in
    [uu____5623]  in
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
    let uu____5729 =
      let uu____5730 =
        let uu____5738 =
          let uu____5739 = FStar_TypeChecker_Env.get_range env  in
          let uu____5740 =
            let uu____5751 =
              let uu____5752 =
                let uu____5757 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5757, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5752  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5751)  in
          FStar_SMTEncoding_Term.mkForall uu____5739 uu____5740  in
        (uu____5738, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5730  in
    [uu____5729]  in
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
    let uu____5847 =
      let uu____5848 =
        let uu____5856 =
          let uu____5857 = FStar_TypeChecker_Env.get_range env  in
          let uu____5858 =
            let uu____5869 =
              let uu____5870 =
                let uu____5875 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5875, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5870  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5869)  in
          FStar_SMTEncoding_Term.mkForall uu____5857 uu____5858  in
        (uu____5856, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5848  in
    [uu____5847]  in
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
    let uu____5975 =
      let uu____5976 =
        let uu____5984 =
          let uu____5985 = FStar_TypeChecker_Env.get_range env  in
          let uu____5986 =
            let uu____5997 =
              let uu____5998 =
                let uu____6003 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____6003, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5998  in
            ([[l_imp_a_b]], [aa; bb], uu____5997)  in
          FStar_SMTEncoding_Term.mkForall uu____5985 uu____5986  in
        (uu____5984, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5976  in
    [uu____5975]  in
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
    let uu____6087 =
      let uu____6088 =
        let uu____6096 =
          let uu____6097 = FStar_TypeChecker_Env.get_range env  in
          let uu____6098 =
            let uu____6109 =
              let uu____6110 =
                let uu____6115 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____6115, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____6110  in
            ([[l_iff_a_b]], [aa; bb], uu____6109)  in
          FStar_SMTEncoding_Term.mkForall uu____6097 uu____6098  in
        (uu____6096, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6088  in
    [uu____6087]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____6186 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____6186  in
    let uu____6191 =
      let uu____6192 =
        let uu____6200 =
          let uu____6201 = FStar_TypeChecker_Env.get_range env  in
          let uu____6202 =
            let uu____6213 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____6213)  in
          FStar_SMTEncoding_Term.mkForall uu____6201 uu____6202  in
        (uu____6200, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6192  in
    [uu____6191]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____6266 =
      let uu____6267 =
        let uu____6275 =
          let uu____6276 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____6276 range_ty  in
        let uu____6277 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____6275, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____6277)
         in
      FStar_SMTEncoding_Util.mkAssume uu____6267  in
    [uu____6266]  in
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
        let uu____6323 = FStar_SMTEncoding_Term.n_fuel Prims.int_one  in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____6323 x1 t  in
      let uu____6325 = FStar_TypeChecker_Env.get_range env  in
      let uu____6326 =
        let uu____6337 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____6337)  in
      FStar_SMTEncoding_Term.mkForall uu____6325 uu____6326  in
    let uu____6362 =
      let uu____6363 =
        let uu____6371 =
          let uu____6372 = FStar_TypeChecker_Env.get_range env  in
          let uu____6373 =
            let uu____6384 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____6384)  in
          FStar_SMTEncoding_Term.mkForall uu____6372 uu____6373  in
        (uu____6371,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6363  in
    [uu____6362]  in
  let mk_with_type_axiom env with_type tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort)
       in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort)
       in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type, [t; e])  in
    let uu____6445 =
      let uu____6446 =
        let uu____6454 =
          let uu____6455 = FStar_TypeChecker_Env.get_range env  in
          let uu____6456 =
            let uu____6472 =
              let uu____6473 =
                let uu____6478 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6479 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6478, uu____6479)  in
              FStar_SMTEncoding_Util.mkAnd uu____6473  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu____6472)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6455 uu____6456  in
        (uu____6454,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6446  in
    [uu____6445]  in
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
          let uu____7037 =
            FStar_Util.find_opt
              (fun uu____7075  ->
                 match uu____7075 with
                 | (l,uu____7091) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____7037 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____7134,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7195 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____7195 with
        | (form,decls) ->
            let uu____7204 =
              let uu____7207 =
                let uu____7210 =
                  let uu____7211 =
                    let uu____7219 =
                      let uu____7220 =
                        let uu____7222 = FStar_Ident.string_of_lid lid  in
                        Prims.op_Hat "Lemma: " uu____7222  in
                      FStar_Pervasives_Native.Some uu____7220  in
                    let uu____7226 =
                      let uu____7228 = FStar_Ident.string_of_lid lid  in
                      Prims.op_Hat "lemma_" uu____7228  in
                    (form, uu____7219, uu____7226)  in
                  FStar_SMTEncoding_Util.mkAssume uu____7211  in
                [uu____7210]  in
              FStar_All.pipe_right uu____7207
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____7204
  
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
              let uu____7286 =
                ((let uu____7290 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____7290) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____7286
              then
                let arg_sorts =
                  let uu____7302 =
                    let uu____7303 = FStar_Syntax_Subst.compress t_norm  in
                    uu____7303.FStar_Syntax_Syntax.n  in
                  match uu____7302 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7309) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____7347  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____7354 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____7356 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____7356 with
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
                    let uu____7388 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____7388, env1)
              else
                (let uu____7393 = prims.is lid  in
                 if uu____7393
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____7402 = prims.mk lid vname  in
                   match uu____7402 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____7426 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____7426, env1)
                 else
                   (let encode_non_total_function_typ =
                      let uu____7433 = FStar_Ident.nsstr lid  in
                      uu____7433 <> "Prims"  in
                    let uu____7437 =
                      let uu____7456 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7456 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7484 =
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7484
                            then
                              let uu____7489 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___316_7492 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___316_7492.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___316_7492.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___316_7492.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___316_7492.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___316_7492.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___316_7492.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___316_7492.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___316_7492.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___316_7492.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___316_7492.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___316_7492.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___316_7492.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___316_7492.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___316_7492.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___316_7492.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___316_7492.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___316_7492.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___316_7492.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___316_7492.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___316_7492.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___316_7492.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___316_7492.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___316_7492.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___316_7492.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___316_7492.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___316_7492.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___316_7492.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___316_7492.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___316_7492.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___316_7492.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___316_7492.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___316_7492.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___316_7492.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___316_7492.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___316_7492.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___316_7492.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___316_7492.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___316_7492.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___316_7492.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___316_7492.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___316_7492.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___316_7492.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___316_7492.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___316_7492.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___316_7492.FStar_TypeChecker_Env.erasable_types_tab)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7489
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7515 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7515)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____7437 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7621  ->
                                  match uu___0_7621 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7625 = FStar_Util.prefix vars
                                         in
                                      (match uu____7625 with
                                       | (uu____7658,xxv) ->
                                           let xx =
                                             let uu____7697 =
                                               let uu____7698 =
                                                 let uu____7704 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7704,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7698
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7697
                                              in
                                           let uu____7707 =
                                             let uu____7708 =
                                               let uu____7716 =
                                                 let uu____7717 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7718 =
                                                   let uu____7729 =
                                                     let uu____7730 =
                                                       let uu____7735 =
                                                         let uu____7736 =
                                                           let uu____7737 =
                                                             let uu____7739 =
                                                               FStar_Ident.string_of_lid
                                                                 d
                                                                in
                                                             FStar_SMTEncoding_Env.escape
                                                               uu____7739
                                                              in
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             uu____7737 xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7736
                                                          in
                                                       (vapp, uu____7735)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7730
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7729)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7717 uu____7718
                                                  in
                                               let uu____7749 =
                                                 let uu____7751 =
                                                   let uu____7753 =
                                                     FStar_Ident.string_of_lid
                                                       d
                                                      in
                                                   FStar_SMTEncoding_Env.escape
                                                     uu____7753
                                                    in
                                                 Prims.op_Hat
                                                   "disc_equation_"
                                                   uu____7751
                                                  in
                                               (uu____7716,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 uu____7749)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7708
                                              in
                                           [uu____7707])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7761 = FStar_Util.prefix vars
                                         in
                                      (match uu____7761 with
                                       | (uu____7794,xxv) ->
                                           let xx =
                                             let uu____7833 =
                                               let uu____7834 =
                                                 let uu____7840 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7840,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7834
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7833
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
                                           let uu____7851 =
                                             let uu____7852 =
                                               let uu____7860 =
                                                 let uu____7861 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7862 =
                                                   let uu____7873 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7873)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7861 uu____7862
                                                  in
                                               (uu____7860,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7852
                                              in
                                           [uu____7851])
                                  | uu____7886 -> []))
                           in
                        let uu____7887 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7887 with
                         | (vars,guards,env',decls1,uu____7912) ->
                             let uu____7925 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7938 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7938, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7942 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7942 with
                                    | (g,ds) ->
                                        let uu____7955 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7955,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7925 with
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
                                  let should_thunk uu____7978 =
                                    let is_type t =
                                      let uu____7986 =
                                        let uu____7987 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7987.FStar_Syntax_Syntax.n  in
                                      match uu____7986 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7991 -> true
                                      | uu____7993 -> false  in
                                    let is_squash t =
                                      let uu____8002 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____8002 with
                                      | (head,uu____8021) ->
                                          let uu____8046 =
                                            let uu____8047 =
                                              FStar_Syntax_Util.un_uinst head
                                               in
                                            uu____8047.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____8046 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____8052;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____8053;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____8055;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____8056;_};_},uu____8057)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____8065 -> false)
                                       in
                                    (((let uu____8069 = FStar_Ident.nsstr lid
                                          in
                                       uu____8069 <> "Prims") &&
                                        (let uu____8074 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____8074))
                                       &&
                                       (let uu____8080 = is_squash t_norm  in
                                        Prims.op_Negation uu____8080))
                                      &&
                                      (let uu____8083 = is_type t_norm  in
                                       Prims.op_Negation uu____8083)
                                     in
                                  let uu____8085 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____8144 -> (false, vars)  in
                                  (match uu____8085 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____8194 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____8194 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____8226 =
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
                                              | uu____8247 ->
                                                  let uu____8256 =
                                                    let uu____8264 =
                                                      get_vtok ()  in
                                                    (uu____8264, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8256
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____8271 =
                                                let uu____8279 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____8279)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____8271
                                               in
                                            let uu____8293 =
                                              let vname_decl =
                                                let uu____8301 =
                                                  let uu____8313 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____8313,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____8301
                                                 in
                                              let uu____8324 =
                                                let env2 =
                                                  let uu___411_8330 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___411_8330.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____8331 =
                                                  let uu____8333 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____8333
                                                   in
                                                if uu____8331
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____8324 with
                                              | (tok_typing,decls2) ->
                                                  let uu____8350 =
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
                                                        let uu____8376 =
                                                          let uu____8379 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8379
                                                           in
                                                        let uu____8386 =
                                                          let uu____8387 =
                                                            let uu____8390 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun uu____8396
                                                                  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____8396)
                                                              uu____8390
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____8387
                                                           in
                                                        (uu____8376,
                                                          uu____8386)
                                                    | uu____8399 when thunked
                                                        -> (decls2, env1)
                                                    | uu____8412 ->
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
                                                          let uu____8436 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8437 =
                                                            let uu____8448 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8448)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8436
                                                            uu____8437
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8458 =
                                                            let uu____8466 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8466,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8458
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
                                                            let uu____8477 =
                                                              let uu____8478
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8478]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8477
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8505 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8506 =
                                                              let uu____8517
                                                                =
                                                                let uu____8518
                                                                  =
                                                                  let uu____8523
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8524
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8523,
                                                                    uu____8524)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8518
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8517)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8505
                                                              uu____8506
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8553 =
                                                          let uu____8556 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8556
                                                           in
                                                        (uu____8553, env1)
                                                     in
                                                  (match uu____8350 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8577 =
                                                         let uu____8580 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8580
                                                           tok_decl
                                                          in
                                                       (uu____8577, env2))
                                               in
                                            (match uu____8293 with
                                             | (decls2,env2) ->
                                                 let uu____8599 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8609 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8609 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8624 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8624, decls)
                                                    in
                                                 (match uu____8599 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8639 =
                                                          let uu____8647 =
                                                            let uu____8648 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8649 =
                                                              let uu____8660
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8660)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8648
                                                              uu____8649
                                                             in
                                                          (uu____8647,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8639
                                                         in
                                                      let freshness =
                                                        let uu____8676 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8676
                                                        then
                                                          let uu____8684 =
                                                            let uu____8685 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8686 =
                                                              let uu____8699
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8706
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8699,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8706)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8685
                                                              uu____8686
                                                             in
                                                          let uu____8712 =
                                                            let uu____8715 =
                                                              let uu____8716
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8716
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8715]  in
                                                          uu____8684 ::
                                                            uu____8712
                                                        else []  in
                                                      let g =
                                                        let uu____8722 =
                                                          let uu____8725 =
                                                            let uu____8728 =
                                                              let uu____8731
                                                                =
                                                                let uu____8734
                                                                  =
                                                                  let uu____8737
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8737
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8734
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8731
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8728
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8725
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8722
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
          let uu____8777 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8777 with
          | FStar_Pervasives_Native.None  ->
              let uu____8788 = encode_free_var false env x t t_norm []  in
              (match uu____8788 with
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
            let uu____8851 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8851 with
            | (decls,env1) ->
                let uu____8862 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8862
                then
                  let uu____8869 =
                    let uu____8870 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8870  in
                  (uu____8869, env1)
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
             (fun uu____8926  ->
                fun lb  ->
                  match uu____8926 with
                  | (decls,env1) ->
                      let uu____8946 =
                        let uu____8951 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8951
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8946 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8980 = FStar_Syntax_Util.head_and_args t  in
    match uu____8980 with
    | (hd,args) ->
        let uu____9024 =
          let uu____9025 = FStar_Syntax_Util.un_uinst hd  in
          uu____9025.FStar_Syntax_Syntax.n  in
        (match uu____9024 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____9031,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             let uu____9054 = FStar_Ident.string_of_lid effect_name  in
             FStar_Util.starts_with "FStar.Tactics" uu____9054
         | uu____9057 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____9068 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___495_9076 = en  in
    let uu____9077 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___495_9076.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___495_9076.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___495_9076.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___495_9076.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___495_9076.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___495_9076.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___495_9076.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___495_9076.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___495_9076.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___495_9076.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9077
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____9107  ->
      fun quals  ->
        match uu____9107 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____9212 = FStar_Util.first_N nbinders formals  in
              match uu____9212 with
              | (formals1,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____9309  ->
                         fun uu____9310  ->
                           match (uu____9309, uu____9310) with
                           | ((formal,uu____9336),(binder,uu____9338)) ->
                               let uu____9359 =
                                 let uu____9366 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9366)  in
                               FStar_Syntax_Syntax.NT uu____9359) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9380 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9421  ->
                              match uu____9421 with
                              | (x,i) ->
                                  let uu____9440 =
                                    let uu___521_9441 = x  in
                                    let uu____9442 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___521_9441.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___521_9441.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9442
                                    }  in
                                  (uu____9440, i)))
                       in
                    FStar_All.pipe_right uu____9380
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9466 =
                      let uu____9471 = FStar_Syntax_Subst.compress body  in
                      let uu____9472 =
                        let uu____9473 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9473
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9471 uu____9472
                       in
                    uu____9466 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___528_9522 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___528_9522.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___528_9522.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___528_9522.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___528_9522.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___528_9522.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___528_9522.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___528_9522.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___528_9522.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___528_9522.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___528_9522.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___528_9522.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___528_9522.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___528_9522.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___528_9522.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___528_9522.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___528_9522.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___528_9522.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___528_9522.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___528_9522.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___528_9522.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___528_9522.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___528_9522.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___528_9522.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___528_9522.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___528_9522.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___528_9522.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___528_9522.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___528_9522.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___528_9522.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___528_9522.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___528_9522.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___528_9522.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___528_9522.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___528_9522.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___528_9522.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___528_9522.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___528_9522.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___528_9522.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___528_9522.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___528_9522.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___528_9522.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___528_9522.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___528_9522.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___528_9522.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___528_9522.FStar_TypeChecker_Env.erasable_types_tab)
                }  in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu____9594  ->
                       fun uu____9595  ->
                         match (uu____9594, uu____9595) with
                         | ((x,uu____9621),(b,uu____9623)) ->
                             let uu____9644 =
                               let uu____9651 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9651)  in
                             FStar_Syntax_Syntax.NT uu____9644) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst comp  in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu____9676 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9676
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9705 ->
                    let uu____9712 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm uu____9712
                | uu____9713 when Prims.op_Negation norm ->
                    let t_norm =
                      norm_with_steps
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
                | uu____9716 ->
                    let uu____9717 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9717)
                 in
              let aux t1 e1 =
                let uu____9759 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9759 with
                | (binders,body,lopt) ->
                    let uu____9791 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9807 -> arrow_formals_comp_norm false t1  in
                    (match uu____9791 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9841 =
                           if nformals < nbinders
                           then
                             let uu____9875 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9875 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9955 = subst_comp formals bs0 comp
                                    in
                                 (bs0, body1, uu____9955)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9985 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9985 with
                                | (binders1,body1) ->
                                    let uu____10038 =
                                      subst_comp formals binders1 comp  in
                                    (binders1, body1, uu____10038))
                             else
                               (let uu____10051 =
                                  subst_comp formals binders comp  in
                                (binders, body, uu____10051))
                            in
                         (match uu____9841 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10111 = aux t e  in
              match uu____10111 with
              | (binders,body,comp) ->
                  let uu____10157 =
                    let uu____10168 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp
                       in
                    if uu____10168
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body  in
                      let uu____10183 = aux comp1 body1  in
                      match uu____10183 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10157 with
                   | (binders1,body1,comp1) ->
                       let uu____10266 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10266, comp1))
               in
            (try
               (fun uu___598_10293  ->
                  match () with
                  | () ->
                      let uu____10300 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10300
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10316 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10379  ->
                                   fun lb  ->
                                     match uu____10379 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10434 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10434
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10440 =
                                             let uu____10449 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10449
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10440 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10316 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10590;
                                    FStar_Syntax_Syntax.lbeff = uu____10591;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10593;
                                    FStar_Syntax_Syntax.lbpos = uu____10594;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10618 =
                                     let uu____10625 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10625 with
                                     | (tcenv',uu____10641,e_t) ->
                                         let uu____10647 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10658 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10647 with
                                          | (e1,t_norm1) ->
                                              ((let uu___661_10675 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___661_10675.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10618 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10685 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10685 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10705 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10705
                                               then
                                                 let uu____10710 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10713 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10710 uu____10713
                                               else ());
                                              (let uu____10718 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10718 with
                                               | (vars,_guards,env'1,binder_decls,uu____10745)
                                                   ->
                                                   let uu____10758 =
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
                                                         let uu____10775 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10775
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10797 =
                                                          let uu____10798 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10799 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10798 fvb
                                                            uu____10799
                                                           in
                                                        (vars, uu____10797))
                                                      in
                                                   (match uu____10758 with
                                                    | (vars1,app) ->
                                                        let uu____10810 =
                                                          let is_logical =
                                                            let uu____10823 =
                                                              let uu____10824
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10824.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10823
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10830 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10834 =
                                                              let uu____10835
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10835
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10834
                                                              (fun lid  ->
                                                                 let uu____10844
                                                                   =
                                                                   let uu____10845
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid  in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu____10845
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10844
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10846 =
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
                                                          if uu____10846
                                                          then
                                                            let uu____10862 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10863 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10862,
                                                              uu____10863)
                                                          else
                                                            (let uu____10874
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10874))
                                                           in
                                                        (match uu____10810
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10898
                                                                 =
                                                                 let uu____10906
                                                                   =
                                                                   let uu____10907
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10908
                                                                    =
                                                                    let uu____10919
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10919)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10907
                                                                    uu____10908
                                                                    in
                                                                 let uu____10928
                                                                   =
                                                                   let uu____10929
                                                                    =
                                                                    let uu____10931
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid  in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu____10931
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10929
                                                                    in
                                                                 (uu____10906,
                                                                   uu____10928,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10898
                                                                in
                                                             let uu____10937
                                                               =
                                                               let uu____10940
                                                                 =
                                                                 let uu____10943
                                                                   =
                                                                   let uu____10946
                                                                    =
                                                                    let uu____10949
                                                                    =
                                                                    let uu____10952
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10952
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10949
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10946
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10943
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10940
                                                                in
                                                             (uu____10937,
                                                               env2)))))))
                               | uu____10961 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____11021 =
                                   let uu____11027 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____11027,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____11021  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____11033 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11086  ->
                                         fun fvb  ->
                                           match uu____11086 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11141 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11141
                                                  in
                                               let gtok =
                                                 let uu____11145 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11145
                                                  in
                                               let env4 =
                                                 let uu____11148 =
                                                   let uu____11151 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun uu____11157  ->
                                                        FStar_Pervasives_Native.Some
                                                          uu____11157)
                                                     uu____11151
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11148
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____11033 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11277
                                     t_norm uu____11279 =
                                     match (uu____11277, uu____11279) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11309;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11310;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11312;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11313;_})
                                         ->
                                         let uu____11340 =
                                           let uu____11347 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11347 with
                                           | (tcenv',uu____11363,e_t) ->
                                               let uu____11369 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11380 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11369 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___748_11397 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___748_11397.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11340 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11410 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11410
                                                then
                                                  let uu____11415 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11417 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11419 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11415 uu____11417
                                                    uu____11419
                                                else ());
                                               (let uu____11424 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11424 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11451 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11451 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11473 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11473
                                                           then
                                                             let uu____11478
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11480
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11483
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11485
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11478
                                                               uu____11480
                                                               uu____11483
                                                               uu____11485
                                                           else ());
                                                          (let uu____11490 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11490
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11519)
                                                               ->
                                                               let uu____11532
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11545
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11545,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11549
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11549
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11562
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11562,
                                                                    decls0))
                                                                  in
                                                               (match uu____11532
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
                                                                    let uu____11583
                                                                    =
                                                                    let uu____11595
                                                                    =
                                                                    let uu____11598
                                                                    =
                                                                    let uu____11601
                                                                    =
                                                                    let uu____11604
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11604
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11601
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11598
                                                                     in
                                                                    (g,
                                                                    uu____11595,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11583
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
                                                                    let uu____11634
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11634
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
                                                                    let uu____11649
                                                                    =
                                                                    let uu____11652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11652
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11649
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11658
                                                                    =
                                                                    let uu____11661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11661
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11658
                                                                     in
                                                                    let uu____11666
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11666
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11682
                                                                    =
                                                                    let uu____11690
                                                                    =
                                                                    let uu____11691
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11692
                                                                    =
                                                                    let uu____11708
                                                                    =
                                                                    let uu____11709
                                                                    =
                                                                    let uu____11714
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11714)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11709
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11708)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11691
                                                                    uu____11692
                                                                     in
                                                                    let uu____11728
                                                                    =
                                                                    let uu____11729
                                                                    =
                                                                    let uu____11731
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu____11731
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11729
                                                                     in
                                                                    (uu____11690,
                                                                    uu____11728,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11682
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11738
                                                                    =
                                                                    let uu____11746
                                                                    =
                                                                    let uu____11747
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11748
                                                                    =
                                                                    let uu____11759
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11759)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11747
                                                                    uu____11748
                                                                     in
                                                                    (uu____11746,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11738
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11773
                                                                    =
                                                                    let uu____11781
                                                                    =
                                                                    let uu____11782
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11783
                                                                    =
                                                                    let uu____11794
                                                                    =
                                                                    let uu____11795
                                                                    =
                                                                    let uu____11800
                                                                    =
                                                                    let uu____11801
                                                                    =
                                                                    let uu____11804
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero
                                                                     in
                                                                    uu____11804
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11801
                                                                     in
                                                                    (gsapp,
                                                                    uu____11800)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11795
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11794)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11782
                                                                    uu____11783
                                                                     in
                                                                    (uu____11781,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11773
                                                                     in
                                                                    let uu____11818
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
                                                                    let uu____11830
                                                                    =
                                                                    let uu____11831
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11831
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11830
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu____11835
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11835
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11844
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11845
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu____11845
                                                                     in
                                                                    let uu____11847
                                                                    =
                                                                    let uu____11855
                                                                    =
                                                                    let uu____11856
                                                                    =
                                                                    let uu____11861
                                                                    =
                                                                    let uu____11862
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11863
                                                                    =
                                                                    let uu____11874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11874)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11862
                                                                    uu____11863
                                                                     in
                                                                    (uu____11861,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11856
                                                                     in
                                                                    (uu____11855,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11847
                                                                     in
                                                                    let uu____11887
                                                                    =
                                                                    let uu____11896
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11896
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11911
                                                                    =
                                                                    let uu____11914
                                                                    =
                                                                    let uu____11915
                                                                    =
                                                                    let uu____11923
                                                                    =
                                                                    let uu____11924
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11925
                                                                    =
                                                                    let uu____11936
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11936)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11924
                                                                    uu____11925
                                                                     in
                                                                    (uu____11923,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11915
                                                                     in
                                                                    [uu____11914]
                                                                     in
                                                                    (d3,
                                                                    uu____11911)
                                                                     in
                                                                    match uu____11887
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11818
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11993
                                                                    =
                                                                    let uu____11996
                                                                    =
                                                                    let uu____11999
                                                                    =
                                                                    let uu____12002
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____12002
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11999
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11996
                                                                     in
                                                                    let uu____12009
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11993,
                                                                    uu____12009,
                                                                    env02))))))))))
                                      in
                                   let uu____12014 =
                                     let uu____12027 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12090  ->
                                          fun uu____12091  ->
                                            match (uu____12090, uu____12091)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12216 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12216 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____12027
                                      in
                                   (match uu____12014 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12283 =
                                          let isDeclFun uu___1_12300 =
                                            match uu___1_12300 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12302 -> true
                                            | uu____12315 -> false  in
                                          let uu____12317 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12317
                                            (fun decls3  ->
                                               let uu____12347 =
                                                 FStar_List.fold_left
                                                   (fun uu____12378  ->
                                                      fun elt  ->
                                                        match uu____12378
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12419 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12419
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12447
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12447
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
                                                                    let uu___846_12485
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___846_12485.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___846_12485.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___846_12485.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12347 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12517 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12517, elts, rest))
                                           in
                                        (match uu____12283 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12546 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12552  ->
                                        match uu___2_12552 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12555 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12563 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12563)))
                                in
                             if uu____12546
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___863_12585  ->
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
                                | FStar_SMTEncoding_Env.Inner_let_rec names
                                    ->
                                    let plural =
                                      (FStar_List.length names) >
                                        Prims.int_one
                                       in
                                    let r =
                                      let uu____12630 = FStar_List.hd names
                                         in
                                      FStar_All.pipe_right uu____12630
                                        FStar_Pervasives_Native.snd
                                       in
                                    ((let uu____12648 =
                                        let uu____12658 =
                                          let uu____12666 =
                                            let uu____12668 =
                                              let uu____12670 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names
                                                 in
                                              FStar_All.pipe_right
                                                uu____12670
                                                (FStar_String.concat ",")
                                               in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12668
                                              (if plural
                                               then "their"
                                               else "its")
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12666, r)
                                           in
                                        [uu____12658]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12648);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12729 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12729
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12748 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12748, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12804 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12804 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l  in
      let uu____12810 = encode_sigelt' env se  in
      match uu____12810 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12822 =
                  let uu____12825 =
                    let uu____12826 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12826  in
                  [uu____12825]  in
                FStar_All.pipe_right uu____12822
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12831 ->
                let uu____12832 =
                  let uu____12835 =
                    let uu____12838 =
                      let uu____12839 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12839  in
                    [uu____12838]  in
                  FStar_All.pipe_right uu____12835
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12846 =
                  let uu____12849 =
                    let uu____12852 =
                      let uu____12855 =
                        let uu____12856 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12856  in
                      [uu____12855]  in
                    FStar_All.pipe_right uu____12852
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12849  in
                FStar_List.append uu____12832 uu____12846
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12870 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12870
       then
         let uu____12875 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12875
       else ());
      (let is_opaque_to_smt t =
         let uu____12887 =
           let uu____12888 = FStar_Syntax_Subst.compress t  in
           uu____12888.FStar_Syntax_Syntax.n  in
         match uu____12887 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12893)) -> s = "opaque_to_smt"
         | uu____12898 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12907 =
           let uu____12908 = FStar_Syntax_Subst.compress t  in
           uu____12908.FStar_Syntax_Syntax.n  in
         match uu____12907 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12913)) -> s = "uninterpreted_by_smt"
         | uu____12918 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____12924 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu____12936 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12954 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12955 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12968 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____12969 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____12980 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12990 =
             let uu____12992 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12992  in
           if uu____12990
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____13021 ->
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
                  let uu____13054 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____13054  in
                let uu____13055 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____13055 with
                | (formals,uu____13067) ->
                    let arity = FStar_List.length formals  in
                    let uu____13075 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____13075 with
                     | (aname,atok,env2) ->
                         let uu____13097 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____13097 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____13113 =
                                  let uu____13114 =
                                    let uu____13126 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13146  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____13126,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____13114
                                   in
                                [uu____13113;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13163 =
                                let aux uu____13209 uu____13210 =
                                  match (uu____13209, uu____13210) with
                                  | ((bv,uu____13254),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13286 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13286 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13309 =
                                             let uu____13312 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13312 :: acc_sorts  in
                                           (env4, uu____13309, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13163 with
                               | (uu____13344,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13360 =
                                       let uu____13368 =
                                         let uu____13369 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13370 =
                                           let uu____13381 =
                                             let uu____13382 =
                                               let uu____13387 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13387)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13382
                                              in
                                           ([[app]], xs_sorts, uu____13381)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13369 uu____13370
                                          in
                                       (uu____13368,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13360
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13402 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13402
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13405 =
                                       let uu____13413 =
                                         let uu____13414 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13415 =
                                           let uu____13426 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13426)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13414 uu____13415
                                          in
                                       (uu____13413,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13405
                                      in
                                   let uu____13439 =
                                     let uu____13442 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13442  in
                                   (env2, uu____13439))))
                 in
              let uu____13451 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13451 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13477,uu____13478)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13479 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4))
              in
           (match uu____13479 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13501,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13508 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13514  ->
                       match uu___3_13514 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13517 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13523 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13526 -> false))
                in
             Prims.op_Negation uu____13508  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13536 =
                let uu____13541 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13541 env fv t quals  in
              match uu____13536 with
              | (decls,env1) ->
                  let tname = FStar_Ident.string_of_lid lid  in
                  let tsym =
                    let uu____13555 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13555  in
                  let uu____13558 =
                    let uu____13559 =
                      let uu____13562 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13562
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13559  in
                  (uu____13558, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13572 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13572 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1008_13584 = env  in
                  let uu____13585 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1008_13584.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1008_13584.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1008_13584.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13585;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1008_13584.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1008_13584.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1008_13584.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1008_13584.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1008_13584.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1008_13584.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1008_13584.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13587 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13587 with
                 | (f3,decls) ->
                     let g =
                       let uu____13601 =
                         let uu____13604 =
                           let uu____13605 =
                             let uu____13613 =
                               let uu____13614 =
                                 let uu____13616 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13616
                                  in
                               FStar_Pervasives_Native.Some uu____13614  in
                             let uu____13620 =
                               let uu____13622 =
                                 let uu____13624 =
                                   FStar_Ident.string_of_lid l  in
                                 Prims.op_Hat "assumption_" uu____13624  in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu____13622
                                in
                             (f3, uu____13613, uu____13620)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13605  in
                         [uu____13604]  in
                       FStar_All.pipe_right uu____13601
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13633) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13647 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13669 =
                        let uu____13672 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13672.FStar_Syntax_Syntax.fv_name  in
                      uu____13669.FStar_Syntax_Syntax.v  in
                    let uu____13673 =
                      let uu____13675 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13675  in
                    if uu____13673
                    then
                      let val_decl =
                        let uu___1025_13707 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1025_13707.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1025_13707.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1025_13707.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1025_13707.FStar_Syntax_Syntax.sigopts)
                        }  in
                      let uu____13708 = encode_sigelt' env1 val_decl  in
                      match uu____13708 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13647 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13744,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                           FStar_Syntax_Syntax.lbunivs = uu____13746;
                           FStar_Syntax_Syntax.lbtyp = uu____13747;
                           FStar_Syntax_Syntax.lbeff = uu____13748;
                           FStar_Syntax_Syntax.lbdef = uu____13749;
                           FStar_Syntax_Syntax.lbattrs = uu____13750;
                           FStar_Syntax_Syntax.lbpos = uu____13751;_}::[]),uu____13752)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu____13771 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one
              in
           (match uu____13771 with
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
                  let uu____13809 =
                    let uu____13812 =
                      let uu____13813 =
                        let uu____13821 =
                          let uu____13822 =
                            FStar_Syntax_Syntax.range_of_fv b2t  in
                          let uu____13823 =
                            let uu____13834 =
                              let uu____13835 =
                                let uu____13840 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13840)  in
                              FStar_SMTEncoding_Util.mkEq uu____13835  in
                            ([[b2t_x]], [xx], uu____13834)  in
                          FStar_SMTEncoding_Term.mkForall uu____13822
                            uu____13823
                           in
                        (uu____13821,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13813  in
                    [uu____13812]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13809
                   in
                let uu____13878 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13878, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13881,uu____13882) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13892  ->
                   match uu___4_13892 with
                   | FStar_Syntax_Syntax.Discriminator uu____13894 -> true
                   | uu____13896 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13898,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13910 =
                      let uu____13912 =
                        let uu____13913 = FStar_Ident.ns_of_lid l  in
                        FStar_List.hd uu____13913  in
                      FStar_Ident.text_of_id uu____13912  in
                    uu____13910 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13922  ->
                      match uu___5_13922 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13925 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13928) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13942  ->
                   match uu___6_13942 with
                   | FStar_Syntax_Syntax.Projector uu____13944 -> true
                   | uu____13950 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13954 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13954 with
            | FStar_Pervasives_Native.Some uu____13961 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1090_13963 = se  in
                  let uu____13964 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13964;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1090_13963.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1090_13963.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1090_13963.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1090_13963.FStar_Syntax_Syntax.sigopts)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13967) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1102_13988 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1102_13988.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1102_13988.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1102_13988.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1102_13988.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1102_13988.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13993) ->
           let uu____14002 = encode_sigelts env ses  in
           (match uu____14002 with
            | (g,env1) ->
                let uu____14013 =
                  FStar_List.fold_left
                    (fun uu____14037  ->
                       fun elt  ->
                         match uu____14037 with
                         | (g',inversions) ->
                             let uu____14065 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_14088  ->
                                       match uu___7_14088 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____14090;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____14091;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____14092;_}
                                           -> false
                                       | uu____14099 -> true))
                                in
                             (match uu____14065 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1128_14124 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1128_14124.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1128_14124.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1128_14124.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____14013 with
                 | (g',inversions) ->
                     let uu____14143 =
                       FStar_List.fold_left
                         (fun uu____14174  ->
                            fun elt  ->
                              match uu____14174 with
                              | (decls,elts,rest) ->
                                  let uu____14215 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14224  ->
                                            match uu___8_14224 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14226 -> true
                                            | uu____14239 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14215
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14262 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14283  ->
                                               match uu___9_14283 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14285 -> true
                                               | uu____14298 -> false))
                                        in
                                     match uu____14262 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1150_14329 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1150_14329.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1150_14329.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1150_14329.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____14143 with
                      | (decls,elts,rest) ->
                          let uu____14355 =
                            let uu____14356 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14363 =
                              let uu____14366 =
                                let uu____14369 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14369  in
                              FStar_List.append elts uu____14366  in
                            FStar_List.append uu____14356 uu____14363  in
                          (uu____14355, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14380,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14393 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14393 with
             | (usubst,uvs) ->
                 let uu____14413 =
                   let uu____14420 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14421 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14422 =
                     let uu____14423 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14423 k  in
                   (uu____14420, uu____14421, uu____14422)  in
                 (match uu____14413 with
                  | (env1,tps1,k1) ->
                      let uu____14436 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14436 with
                       | (tps2,k2) ->
                           let uu____14444 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14444 with
                            | (uu____14452,k3) ->
                                let uu____14458 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14458 with
                                 | (tps3,env_tps,uu____14470,us) ->
                                     let u_k =
                                       let uu____14473 =
                                         let uu____14474 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14475 =
                                           let uu____14480 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  Prims.int_zero)
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14482 =
                                             let uu____14483 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14483
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14480 uu____14482
                                            in
                                         uu____14475
                                           FStar_Pervasives_Native.None
                                           uu____14474
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14473 k3
                                        in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14501) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14507,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14510) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  -> universe_leq u1 v))
                                       | (uu____14518,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14525) ->
                                           let uu____14526 =
                                             let uu____14528 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14528
                                              in
                                           failwith uu____14526
                                       | (uu____14532,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14533 =
                                             let uu____14535 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14535
                                              in
                                           failwith uu____14533
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14539,uu____14540) ->
                                           let uu____14551 =
                                             let uu____14553 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14553
                                              in
                                           failwith uu____14551
                                       | (uu____14557,FStar_Syntax_Syntax.U_unif
                                          uu____14558) ->
                                           let uu____14569 =
                                             let uu____14571 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14571
                                              in
                                           failwith uu____14569
                                       | uu____14575 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14588 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14588 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14606 = u_leq_u_k u_tp  in
                                       if uu____14606
                                       then true
                                       else
                                         (let uu____14613 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14613 with
                                          | (formals,uu____14622) ->
                                              let uu____14627 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14627 with
                                               | (uu____14637,uu____14638,uu____14639,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14650 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14650
             then
               let uu____14655 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14655
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14675  ->
                       match uu___10_14675 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14679 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14692 = c  in
                 match uu____14692 with
                 | (name,args,uu____14697,uu____14698,uu____14699) ->
                     let uu____14710 =
                       let uu____14711 =
                         let uu____14723 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14750  ->
                                   match uu____14750 with
                                   | (uu____14759,sort,uu____14761) -> sort))
                            in
                         (name, uu____14723,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14711  in
                     [uu____14710]
               else
                 (let uu____14772 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14772 c)
                in
             let inversion_axioms tapp vars =
               let uu____14790 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14798 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14798 FStar_Option.isNone))
                  in
               if uu____14790
               then []
               else
                 (let uu____14833 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14833 with
                  | (xxsym,xx) ->
                      let uu____14846 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14885  ->
                                fun l  ->
                                  match uu____14885 with
                                  | (out,decls) ->
                                      let uu____14905 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14905 with
                                       | (uu____14916,data_t) ->
                                           let uu____14918 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14918 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14938 =
                                                    let uu____14939 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14939.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14938 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14942,indices)
                                                      -> indices
                                                  | uu____14968 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14998  ->
                                                            match uu____14998
                                                            with
                                                            | (x,uu____15006)
                                                                ->
                                                                let uu____15011
                                                                  =
                                                                  let uu____15012
                                                                    =
                                                                    let uu____15020
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____15020,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____15012
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____15011)
                                                       env)
                                                   in
                                                let uu____15025 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____15025 with
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
                                                             (fun v  ->
                                                                fun a  ->
                                                                  let uu____15060
                                                                    =
                                                                    let uu____15065
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    (uu____15065,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____15060)
                                                             vars indices1
                                                         else []  in
                                                       let uu____15068 =
                                                         let uu____15069 =
                                                           let uu____15074 =
                                                             let uu____15075
                                                               =
                                                               let uu____15080
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____15081
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____15080,
                                                                 uu____15081)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____15075
                                                              in
                                                           (out, uu____15074)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____15069
                                                          in
                                                       (uu____15068,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14846 with
                       | (data_ax,decls) ->
                           let uu____15096 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____15096 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu____15113 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____15113 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____15120 =
                                    let uu____15128 =
                                      let uu____15129 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15130 =
                                        let uu____15141 =
                                          let uu____15142 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15144 =
                                            let uu____15147 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15147 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15142 uu____15144
                                           in
                                        let uu____15149 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15141,
                                          uu____15149)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15129 uu____15130
                                       in
                                    let uu____15158 =
                                      let uu____15160 =
                                        let uu____15162 =
                                          FStar_Ident.string_of_lid t  in
                                        Prims.op_Hat
                                          "fuel_guarded_inversion_"
                                          uu____15162
                                         in
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        uu____15160
                                       in
                                    (uu____15128,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15158)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____15120
                                   in
                                let uu____15168 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15168)))
                in
             let uu____15175 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15189 ->
                     let uu____15190 =
                       let uu____15197 =
                         let uu____15198 =
                           let uu____15213 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15213)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15198  in
                       FStar_Syntax_Syntax.mk uu____15197  in
                     uu____15190 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15175 with
             | (formals,res) ->
                 let uu____15237 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15237 with
                  | (vars,guards,env',binder_decls,uu____15262) ->
                      let arity = FStar_List.length vars  in
                      let uu____15276 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15276 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15302 =
                               let uu____15310 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15310)  in
                             FStar_SMTEncoding_Util.mkApp uu____15302  in
                           let uu____15316 =
                             let tname_decl =
                               let uu____15326 =
                                 let uu____15327 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15346 =
                                             let uu____15348 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15348
                                              in
                                           let uu____15350 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15346, uu____15350, false)))
                                    in
                                 let uu____15354 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15327,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15354, false)
                                  in
                               constructor_or_logic_type_decl uu____15326  in
                             let uu____15362 =
                               match vars with
                               | [] ->
                                   let uu____15375 =
                                     let uu____15376 =
                                       let uu____15379 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____15385  ->
                                            FStar_Pervasives_Native.Some
                                              uu____15385) uu____15379
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15376
                                      in
                                   ([], uu____15375)
                               | uu____15388 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15398 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15398
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15414 =
                                       let uu____15422 =
                                         let uu____15423 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15424 =
                                           let uu____15440 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15440)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15423 uu____15424
                                          in
                                       (uu____15422,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15414
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15362 with
                             | (tok_decls,env2) ->
                                 let uu____15467 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15467
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15316 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15495 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15495 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____15517 =
                                            let uu____15518 =
                                              let uu____15526 =
                                                let uu____15527 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15527
                                                 in
                                              (uu____15526,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15518
                                             in
                                          [uu____15517]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15537 =
                                          FStar_List.map
                                            (fun uu____15541  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15537 true
                                         in
                                      let uu____15543 =
                                        let uu____15546 =
                                          let uu____15549 =
                                            let uu____15552 =
                                              let uu____15553 =
                                                let uu____15561 =
                                                  let uu____15562 =
                                                    let uu____15567 =
                                                      let uu____15568 =
                                                        let uu____15579 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15579)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15568
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15567)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15562
                                                   in
                                                (uu____15561,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15553
                                               in
                                            [uu____15552]  in
                                          FStar_List.append karr uu____15549
                                           in
                                        FStar_All.pipe_right uu____15546
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15543
                                   in
                                let aux =
                                  let uu____15598 =
                                    let uu____15601 =
                                      inversion_axioms tapp vars  in
                                    let uu____15604 =
                                      let uu____15607 =
                                        let uu____15610 =
                                          let uu____15611 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15611 env2 tapp
                                            vars
                                           in
                                        [uu____15610]  in
                                      FStar_All.pipe_right uu____15607
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15601 uu____15604
                                     in
                                  FStar_List.append kindingAx uu____15598  in
                                let g =
                                  let uu____15619 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15619
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15627,uu____15628,uu____15629,uu____15630,uu____15631)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15639,t,uu____15641,n_tps,uu____15643) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15654 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15654 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15678 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15678 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15702 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15702 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15722 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15722 with
                           | (vars,guards,env',binder_decls,names) ->
                               let fields =
                                 FStar_All.pipe_right names
                                   (FStar_List.mapi
                                      (fun n  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15801 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15801,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15808 =
                                   let uu____15809 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15809, true)
                                    in
                                 let uu____15817 =
                                   let uu____15824 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15824
                                    in
                                 FStar_All.pipe_right uu____15808 uu____15817
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
                               let uu____15836 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15836 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15848::uu____15849 ->
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
                                            let uu____15898 =
                                              let uu____15899 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15899]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15898
                                             in
                                          let uu____15925 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15926 =
                                            let uu____15937 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15937)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15925 uu____15926
                                      | uu____15964 -> tok_typing  in
                                    let uu____15975 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15975 with
                                     | (vars',guards',env'',decls_formals,uu____16000)
                                         ->
                                         let uu____16013 =
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
                                         (match uu____16013 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____16043 ->
                                                    let uu____16044 =
                                                      let uu____16045 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16045
                                                       in
                                                    [uu____16044]
                                                 in
                                              let encode_elim uu____16061 =
                                                let uu____16062 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16062 with
                                                | (head,args) ->
                                                    let uu____16113 =
                                                      let uu____16114 =
                                                        FStar_Syntax_Subst.compress
                                                          head
                                                         in
                                                      uu____16114.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16113 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16126;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16127;_},uu____16128)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16134 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16134
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
                                                                  | uu____16197
                                                                    ->
                                                                    let uu____16198
                                                                    =
                                                                    let uu____16204
                                                                    =
                                                                    let uu____16206
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16206
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16204)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16198
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16229
                                                                    =
                                                                    let uu____16231
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16231
                                                                     in
                                                                    if
                                                                    uu____16229
                                                                    then
                                                                    let uu____16253
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16253]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16256
                                                                =
                                                                let uu____16270
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16327
                                                                     ->
                                                                    fun
                                                                    uu____16328
                                                                     ->
                                                                    match 
                                                                    (uu____16327,
                                                                    uu____16328)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16439
                                                                    =
                                                                    let uu____16447
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16447
                                                                     in
                                                                    (match uu____16439
                                                                    with
                                                                    | 
                                                                    (uu____16461,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16472
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16472
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16477
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16477
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
                                                                  uu____16270
                                                                 in
                                                              (match uu____16256
                                                               with
                                                               | (uu____16498,arg_vars,elim_eqns_or_guards,uu____16501)
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
                                                                    let uu____16528
                                                                    =
                                                                    let uu____16536
                                                                    =
                                                                    let uu____16537
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16538
                                                                    =
                                                                    let uu____16549
                                                                    =
                                                                    let uu____16550
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16550
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16552
                                                                    =
                                                                    let uu____16553
                                                                    =
                                                                    let uu____16558
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16558)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16553
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16549,
                                                                    uu____16552)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16537
                                                                    uu____16538
                                                                     in
                                                                    (uu____16536,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16528
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____16573
                                                                    =
                                                                    let uu____16574
                                                                    =
                                                                    let uu____16580
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16580,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16574
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16573
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____16586
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v  ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____16609
                                                                    =
                                                                    let uu____16610
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____16610
                                                                    dapp1  in
                                                                    [uu____16609])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16586
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16617
                                                                    =
                                                                    let uu____16625
                                                                    =
                                                                    let uu____16626
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16627
                                                                    =
                                                                    let uu____16638
                                                                    =
                                                                    let uu____16639
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16639
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16641
                                                                    =
                                                                    let uu____16642
                                                                    =
                                                                    let uu____16647
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16647)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16642
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16638,
                                                                    uu____16641)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16626
                                                                    uu____16627
                                                                     in
                                                                    (uu____16625,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16617
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
                                                         let uu____16666 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16666
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
                                                                  | uu____16729
                                                                    ->
                                                                    let uu____16730
                                                                    =
                                                                    let uu____16736
                                                                    =
                                                                    let uu____16738
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16738
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16736)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16730
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16761
                                                                    =
                                                                    let uu____16763
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16763
                                                                     in
                                                                    if
                                                                    uu____16761
                                                                    then
                                                                    let uu____16785
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16785]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16788
                                                                =
                                                                let uu____16802
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16859
                                                                     ->
                                                                    fun
                                                                    uu____16860
                                                                     ->
                                                                    match 
                                                                    (uu____16859,
                                                                    uu____16860)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16971
                                                                    =
                                                                    let uu____16979
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16979
                                                                     in
                                                                    (match uu____16971
                                                                    with
                                                                    | 
                                                                    (uu____16993,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17004
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17004
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17009
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17009
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
                                                                  uu____16802
                                                                 in
                                                              (match uu____16788
                                                               with
                                                               | (uu____17030,arg_vars,elim_eqns_or_guards,uu____17033)
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
                                                                    let uu____17060
                                                                    =
                                                                    let uu____17068
                                                                    =
                                                                    let uu____17069
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17070
                                                                    =
                                                                    let uu____17081
                                                                    =
                                                                    let uu____17082
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17082
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17084
                                                                    =
                                                                    let uu____17085
                                                                    =
                                                                    let uu____17090
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17090)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17085
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17081,
                                                                    uu____17084)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17069
                                                                    uu____17070
                                                                     in
                                                                    (uu____17068,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17060
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____17105
                                                                    =
                                                                    let uu____17106
                                                                    =
                                                                    let uu____17112
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17112,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17106
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17105
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____17118
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v  ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____17141
                                                                    =
                                                                    let uu____17142
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____17142
                                                                    dapp1  in
                                                                    [uu____17141])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17118
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17149
                                                                    =
                                                                    let uu____17157
                                                                    =
                                                                    let uu____17158
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17159
                                                                    =
                                                                    let uu____17170
                                                                    =
                                                                    let uu____17171
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17171
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17173
                                                                    =
                                                                    let uu____17174
                                                                    =
                                                                    let uu____17179
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17179)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17174
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17170,
                                                                    uu____17173)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17158
                                                                    uu____17159
                                                                     in
                                                                    (uu____17157,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17149
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17196 ->
                                                         ((let uu____17198 =
                                                             let uu____17204
                                                               =
                                                               let uu____17206
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17208
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17206
                                                                 uu____17208
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17204)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17198);
                                                          ([], [])))
                                                 in
                                              let uu____17216 =
                                                encode_elim ()  in
                                              (match uu____17216 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17242 =
                                                       let uu____17245 =
                                                         let uu____17248 =
                                                           let uu____17251 =
                                                             let uu____17254
                                                               =
                                                               let uu____17257
                                                                 =
                                                                 let uu____17260
                                                                   =
                                                                   let uu____17261
                                                                    =
                                                                    let uu____17273
                                                                    =
                                                                    let uu____17274
                                                                    =
                                                                    let uu____17276
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17276
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17274
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17273)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17261
                                                                    in
                                                                 [uu____17260]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17257
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17254
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17287 =
                                                             let uu____17290
                                                               =
                                                               let uu____17293
                                                                 =
                                                                 let uu____17296
                                                                   =
                                                                   let uu____17299
                                                                    =
                                                                    let uu____17302
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17307
                                                                    =
                                                                    let uu____17310
                                                                    =
                                                                    let uu____17311
                                                                    =
                                                                    let uu____17319
                                                                    =
                                                                    let uu____17320
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17321
                                                                    =
                                                                    let uu____17332
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17332)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17320
                                                                    uu____17321
                                                                     in
                                                                    (uu____17319,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17311
                                                                     in
                                                                    let uu____17345
                                                                    =
                                                                    let uu____17348
                                                                    =
                                                                    let uu____17349
                                                                    =
                                                                    let uu____17357
                                                                    =
                                                                    let uu____17358
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17359
                                                                    =
                                                                    let uu____17370
                                                                    =
                                                                    let uu____17371
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17371
                                                                    vars'  in
                                                                    let uu____17373
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17370,
                                                                    uu____17373)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17358
                                                                    uu____17359
                                                                     in
                                                                    (uu____17357,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17349
                                                                     in
                                                                    [uu____17348]
                                                                     in
                                                                    uu____17310
                                                                    ::
                                                                    uu____17345
                                                                     in
                                                                    uu____17302
                                                                    ::
                                                                    uu____17307
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17299
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17296
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17293
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17290
                                                              in
                                                           FStar_List.append
                                                             uu____17251
                                                             uu____17287
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17248
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17245
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17242
                                                      in
                                                   let uu____17390 =
                                                     let uu____17391 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17391 g
                                                      in
                                                   (uu____17390, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17425  ->
              fun se  ->
                match uu____17425 with
                | (g,env1) ->
                    let uu____17445 = encode_sigelt env1 se  in
                    (match uu____17445 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17513 =
        match uu____17513 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17550 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17558 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17558
                   then
                     let uu____17563 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17565 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17567 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17563 uu____17565 uu____17567
                   else ());
                  (let uu____17572 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17572 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17590 =
                         let uu____17598 =
                           let uu____17600 =
                             let uu____17602 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17602
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17600  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17598
                          in
                       (match uu____17590 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17622 = FStar_Options.log_queries ()
                                 in
                              if uu____17622
                              then
                                let uu____17625 =
                                  let uu____17627 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17629 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17631 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17627 uu____17629 uu____17631
                                   in
                                FStar_Pervasives_Native.Some uu____17625
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17647 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17657 =
                                let uu____17660 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17660  in
                              FStar_List.append uu____17647 uu____17657  in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17672,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17692 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17692 with
                  | (g,env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env')))
         in
      let uu____17713 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env)
         in
      match uu____17713 with | (uu____17740,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17793  ->
              match uu____17793 with
              | (l,uu____17802,uu____17803) ->
                  let uu____17806 =
                    let uu____17818 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17818, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17806))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17851  ->
              match uu____17851 with
              | (l,uu____17862,uu____17863) ->
                  let uu____17866 =
                    let uu____17867 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun uu____17870  ->
                         FStar_SMTEncoding_Term.Echo uu____17870) uu____17867
                     in
                  let uu____17871 =
                    let uu____17874 =
                      let uu____17875 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17875  in
                    [uu____17874]  in
                  uu____17866 :: uu____17871))
       in
    (prefix, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17893 =
      let uu____17896 =
        let uu____17897 = FStar_Util.psmap_empty ()  in
        let uu____17912 =
          let uu____17921 = FStar_Util.psmap_empty ()  in (uu____17921, [])
           in
        let uu____17928 =
          let uu____17930 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17930 FStar_Ident.string_of_lid  in
        let uu____17932 = FStar_Util.smap_create (Prims.of_int (100))  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17897;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17912;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17928;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17932
        }  in
      [uu____17896]  in
    FStar_ST.op_Colon_Equals last_env uu____17893
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17976 = FStar_ST.op_Bang last_env  in
      match uu____17976 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18004 ->
          let uu___1574_18007 = e  in
          let uu____18008 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1574_18007.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1574_18007.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1574_18007.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1574_18007.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1574_18007.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1574_18007.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1574_18007.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18008;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1574_18007.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1574_18007.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18016 = FStar_ST.op_Bang last_env  in
    match uu____18016 with
    | [] -> failwith "Empty env stack"
    | uu____18043::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
  
let (push_env : unit -> unit) =
  fun uu____18075  ->
    let uu____18076 = FStar_ST.op_Bang last_env  in
    match uu____18076 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd  in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
  
let (pop_env : unit -> unit) =
  fun uu____18136  ->
    let uu____18137 = FStar_ST.op_Bang last_env  in
    match uu____18137 with
    | [] -> failwith "Popping an empty stack"
    | uu____18164::tl -> FStar_ST.op_Colon_Equals last_env tl
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18201  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18254  ->
         let uu____18255 = snapshot_env ()  in
         match uu____18255 with
         | (env_depth,()) ->
             let uu____18277 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18277 with
              | (varops_depth,()) ->
                  let uu____18299 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18299 with
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
        (fun uu____18357  ->
           let uu____18358 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18358 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18453 = snapshot msg  in () 
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
        | (uu____18499::uu____18500,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1635_18508 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1635_18508.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1635_18508.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1635_18508.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18509 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1641_18536 = elt  in
        let uu____18537 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1641_18536.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1641_18536.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18537;
          FStar_SMTEncoding_Term.a_names =
            (uu___1641_18536.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18557 =
        let uu____18560 =
          let uu____18561 =
            let uu____18562 = FStar_Ident.ns_of_lid lid  in
            FStar_Ident.lid_of_ids uu____18562  in
          FStar_SMTEncoding_Term.Namespace uu____18561  in
        let uu____18563 = open_fact_db_tags env  in uu____18560 ::
          uu____18563
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18557
  
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
      let uu____18590 = encode_sigelt env se  in
      match uu____18590 with
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
                (let uu____18636 =
                   let uu____18639 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18639
                    in
                 match uu____18636 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18654 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18654
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18684 = FStar_Options.log_queries ()  in
        if uu____18684
        then
          let uu____18689 =
            let uu____18690 =
              let uu____18692 =
                let uu____18694 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18694 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18692  in
            FStar_SMTEncoding_Term.Caption uu____18690  in
          uu____18689 :: decls
        else decls  in
      (let uu____18713 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18713
       then
         let uu____18716 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18716
       else ());
      (let env =
         let uu____18722 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18722 tcenv  in
       let uu____18723 = encode_top_level_facts env se  in
       match uu____18723 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18737 =
               let uu____18740 =
                 let uu____18743 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18743
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18740  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18737)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18776 = FStar_Options.log_queries ()  in
          if uu____18776
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1679_18796 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1679_18796.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1679_18796.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1679_18796.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1679_18796.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1679_18796.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1679_18796.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1679_18796.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1679_18796.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1679_18796.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1679_18796.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18801 =
             let uu____18804 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18804
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18801  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18824 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18824
      then ([], [])
      else
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____18857  ->
             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh
               ();
             (let name =
                let uu____18861 =
                  FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format2 "%s %s"
                  (if modul.FStar_Syntax_Syntax.is_interface
                   then "interface"
                   else "module") uu____18861
                 in
              (let uu____18871 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18871
               then
                 let uu____18874 =
                   FStar_All.pipe_right
                     (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                     Prims.string_of_int
                    in
                 FStar_Util.print2
                   "+++++++++++Encoding externals for %s ... %s exports\n"
                   name uu____18874
               else ());
              (let env =
                 let uu____18882 =
                   get_env modul.FStar_Syntax_Syntax.name tcenv  in
                 FStar_All.pipe_right uu____18882
                   FStar_SMTEncoding_Env.reset_current_module_fvbs
                  in
               let encode_signature env1 ses =
                 FStar_All.pipe_right ses
                   (FStar_List.fold_left
                      (fun uu____18921  ->
                         fun se  ->
                           match uu____18921 with
                           | (g,env2) ->
                               let uu____18941 =
                                 encode_top_level_facts env2 se  in
                               (match uu____18941 with
                                | (g',env3) ->
                                    ((FStar_List.append g g'), env3)))
                      ([], env1))
                  in
               let uu____18964 =
                 encode_signature
                   (let uu___1703_18973 = env  in
                    {
                      FStar_SMTEncoding_Env.bvar_bindings =
                        (uu___1703_18973.FStar_SMTEncoding_Env.bvar_bindings);
                      FStar_SMTEncoding_Env.fvar_bindings =
                        (uu___1703_18973.FStar_SMTEncoding_Env.fvar_bindings);
                      FStar_SMTEncoding_Env.depth =
                        (uu___1703_18973.FStar_SMTEncoding_Env.depth);
                      FStar_SMTEncoding_Env.tcenv =
                        (uu___1703_18973.FStar_SMTEncoding_Env.tcenv);
                      FStar_SMTEncoding_Env.warn = false;
                      FStar_SMTEncoding_Env.nolabels =
                        (uu___1703_18973.FStar_SMTEncoding_Env.nolabels);
                      FStar_SMTEncoding_Env.use_zfuel_name =
                        (uu___1703_18973.FStar_SMTEncoding_Env.use_zfuel_name);
                      FStar_SMTEncoding_Env.encode_non_total_function_typ =
                        (uu___1703_18973.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                      FStar_SMTEncoding_Env.current_module_name =
                        (uu___1703_18973.FStar_SMTEncoding_Env.current_module_name);
                      FStar_SMTEncoding_Env.encoding_quantifier =
                        (uu___1703_18973.FStar_SMTEncoding_Env.encoding_quantifier);
                      FStar_SMTEncoding_Env.global_cache =
                        (uu___1703_18973.FStar_SMTEncoding_Env.global_cache)
                    }) modul.FStar_Syntax_Syntax.exports
                  in
               match uu____18964 with
               | (decls,env1) ->
                   (give_decls_to_z3_and_set_env env1 name decls;
                    (let uu____18991 =
                       FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium
                        in
                     if uu____18991
                     then
                       FStar_Util.print1 "Done encoding externals for %s\n"
                         name
                     else ());
                    (let uu____18997 =
                       FStar_All.pipe_right env1
                         FStar_SMTEncoding_Env.get_current_module_fvbs
                        in
                     (decls, uu____18997))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun tcmod  ->
      fun uu____19027  ->
        match uu____19027 with
        | (decls,fvbs) ->
            let uu____19040 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
            if uu____19040
            then ()
            else
              (let name =
                 let uu____19047 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name
                    in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu____19047
                  in
               (let uu____19057 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____19057
                then
                  let uu____19060 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int
                     in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19060
                else ());
               (let env =
                  let uu____19068 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv  in
                  FStar_All.pipe_right uu____19068
                    FStar_SMTEncoding_Env.reset_current_module_fvbs
                   in
                let env1 =
                  let uu____19070 = FStar_All.pipe_right fvbs FStar_List.rev
                     in
                  FStar_All.pipe_right uu____19070
                    (FStar_List.fold_left
                       (fun env1  ->
                          fun fvb  ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env)
                   in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19084 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19084
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
        (let uu____19146 =
           let uu____19148 = FStar_TypeChecker_Env.current_module tcenv  in
           FStar_Ident.string_of_lid uu____19148  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19146);
        (let env =
           let uu____19150 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19150 tcenv  in
         let uu____19151 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19188 = aux rest  in
                 (match uu____19188 with
                  | (out,rest1) ->
                      let t =
                        let uu____19216 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19216 with
                        | FStar_Pervasives_Native.Some uu____19219 ->
                            let uu____19220 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19220
                              x.FStar_Syntax_Syntax.sort
                        | uu____19221 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        norm_with_steps
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19225 =
                        let uu____19228 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1746_19231 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1746_19231.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1746_19231.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19228 :: out  in
                      (uu____19225, rest1))
             | uu____19236 -> ([], bindings)  in
           let uu____19243 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19243 with
           | (closing,bindings) ->
               let uu____19268 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19268, bindings)
            in
         match uu____19151 with
         | (q1,bindings) ->
             let uu____19291 = encode_env_bindings env bindings  in
             (match uu____19291 with
              | (env_decls,env1) ->
                  ((let uu____19313 =
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
                    if uu____19313
                    then
                      let uu____19320 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula {: %s\n"
                        uu____19320
                    else ());
                   (let uu____19325 =
                      FStar_Util.record_time
                        (fun uu____19340  ->
                           FStar_SMTEncoding_EncodeTerm.encode_formula q1
                             env1)
                       in
                    match uu____19325 with
                    | ((phi,qdecls),ms) ->
                        let uu____19364 =
                          let uu____19369 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19369 phi
                           in
                        (match uu____19364 with
                         | (labels,phi1) ->
                             let uu____19386 = encode_labels labels  in
                             (match uu____19386 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19422 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19422
                                    then
                                      let uu____19427 =
                                        let uu____19428 =
                                          let uu____19430 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula : "
                                            uu____19430
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19428
                                         in
                                      [uu____19427]
                                    else []  in
                                  let query_prelude =
                                    let uu____19438 =
                                      let uu____19439 =
                                        let uu____19440 =
                                          let uu____19443 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19450 =
                                            let uu____19453 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19453
                                             in
                                          FStar_List.append uu____19443
                                            uu____19450
                                           in
                                        FStar_List.append env_decls
                                          uu____19440
                                         in
                                      FStar_All.pipe_right uu____19439
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19438
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19463 =
                                      let uu____19471 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19472 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19471,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19472)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19463
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  ((let uu____19485 =
                                      ((FStar_TypeChecker_Env.debug tcenv
                                          FStar_Options.Medium)
                                         ||
                                         (FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")))
                                        ||
                                        (FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug tcenv)
                                           (FStar_Options.Other "SMTQuery"))
                                       in
                                    if uu____19485
                                    then
                                      FStar_Util.print_string
                                        "} Done encoding\n"
                                    else ());
                                   (let uu____19496 =
                                      (((FStar_TypeChecker_Env.debug tcenv
                                           FStar_Options.Medium)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")))
                                         ||
                                         (FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               tcenv)
                                            (FStar_Options.Other "SMTQuery")))
                                        ||
                                        (FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug tcenv)
                                           (FStar_Options.Other "Time"))
                                       in
                                    if uu____19496
                                    then
                                      FStar_Util.print1
                                        "Encoding took %sms\n"
                                        (Prims.string_of_int ms)
                                    else ());
                                   (query_prelude, labels, qry, suffix))))))))
  