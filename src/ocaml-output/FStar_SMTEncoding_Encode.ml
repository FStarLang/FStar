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
              let uu____9210 = FStar_Util.first_N nbinders formals  in
              match uu____9210 with
              | (formals1,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____9305  ->
                         fun uu____9306  ->
                           match (uu____9305, uu____9306) with
                           | ((formal,uu____9332),(binder,uu____9334)) ->
                               let uu____9355 =
                                 let uu____9362 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9362)  in
                               FStar_Syntax_Syntax.NT uu____9355) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9376 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9417  ->
                              match uu____9417 with
                              | (x,i) ->
                                  let uu____9436 =
                                    let uu___521_9437 = x  in
                                    let uu____9438 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___521_9437.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___521_9437.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9438
                                    }  in
                                  (uu____9436, i)))
                       in
                    FStar_All.pipe_right uu____9376
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9460 = FStar_Syntax_Subst.compress body  in
                    let uu____9461 =
                      let uu____9462 =
                        FStar_Syntax_Util.args_of_binders extra_formals1  in
                      FStar_All.pipe_left FStar_Pervasives_Native.snd
                        uu____9462
                       in
                    FStar_Syntax_Syntax.extend_app_n uu____9460 uu____9461
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___528_9509 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___528_9509.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___528_9509.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___528_9509.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___528_9509.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___528_9509.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___528_9509.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___528_9509.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___528_9509.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___528_9509.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___528_9509.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___528_9509.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___528_9509.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___528_9509.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___528_9509.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___528_9509.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___528_9509.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___528_9509.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___528_9509.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___528_9509.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___528_9509.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___528_9509.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___528_9509.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___528_9509.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___528_9509.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___528_9509.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___528_9509.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___528_9509.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___528_9509.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___528_9509.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___528_9509.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___528_9509.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___528_9509.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___528_9509.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___528_9509.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___528_9509.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___528_9509.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___528_9509.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___528_9509.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___528_9509.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___528_9509.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___528_9509.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___528_9509.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___528_9509.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___528_9509.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___528_9509.FStar_TypeChecker_Env.erasable_types_tab)
                }  in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu____9581  ->
                       fun uu____9582  ->
                         match (uu____9581, uu____9582) with
                         | ((x,uu____9608),(b,uu____9610)) ->
                             let uu____9631 =
                               let uu____9638 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9638)  in
                             FStar_Syntax_Syntax.NT uu____9631) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst comp  in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu____9663 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9663
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9692 ->
                    let uu____9699 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm uu____9699
                | uu____9700 when Prims.op_Negation norm ->
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
                | uu____9703 ->
                    let uu____9704 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9704)
                 in
              let aux t1 e1 =
                let uu____9746 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9746 with
                | (binders,body,lopt) ->
                    let uu____9778 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9794 -> arrow_formals_comp_norm false t1  in
                    (match uu____9778 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9828 =
                           if nformals < nbinders
                           then
                             let uu____9862 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9862 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9942 = subst_comp formals bs0 comp
                                    in
                                 (bs0, body1, uu____9942)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9972 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9972 with
                                | (binders1,body1) ->
                                    let uu____10019 =
                                      subst_comp formals binders1 comp  in
                                    (binders1, body1, uu____10019))
                             else
                               (let uu____10032 =
                                  subst_comp formals binders comp  in
                                (binders, body, uu____10032))
                            in
                         (match uu____9828 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10092 = aux t e  in
              match uu____10092 with
              | (binders,body,comp) ->
                  let uu____10138 =
                    let uu____10149 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp
                       in
                    if uu____10149
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body  in
                      let uu____10164 = aux comp1 body1  in
                      match uu____10164 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10138 with
                   | (binders1,body1,comp1) ->
                       let uu____10247 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10247, comp1))
               in
            (try
               (fun uu___598_10274  ->
                  match () with
                  | () ->
                      let uu____10281 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10281
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10297 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10360  ->
                                   fun lb  ->
                                     match uu____10360 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10415 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10415
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10421 =
                                             let uu____10430 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10430
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10421 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10297 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10571;
                                    FStar_Syntax_Syntax.lbeff = uu____10572;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10574;
                                    FStar_Syntax_Syntax.lbpos = uu____10575;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10599 =
                                     let uu____10606 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10606 with
                                     | (tcenv',uu____10622,e_t) ->
                                         let uu____10628 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10639 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10628 with
                                          | (e1,t_norm1) ->
                                              ((let uu___661_10656 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___661_10656.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10599 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10666 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10666 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10686 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10686
                                               then
                                                 let uu____10691 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10694 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10691 uu____10694
                                               else ());
                                              (let uu____10699 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10699 with
                                               | (vars,_guards,env'1,binder_decls,uu____10726)
                                                   ->
                                                   let uu____10739 =
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
                                                         let uu____10756 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10756
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10778 =
                                                          let uu____10779 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10780 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10779 fvb
                                                            uu____10780
                                                           in
                                                        (vars, uu____10778))
                                                      in
                                                   (match uu____10739 with
                                                    | (vars1,app) ->
                                                        let uu____10791 =
                                                          let is_logical =
                                                            let uu____10804 =
                                                              let uu____10805
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10805.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10804
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10811 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10815 =
                                                              let uu____10816
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10816
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10815
                                                              (fun lid  ->
                                                                 let uu____10825
                                                                   =
                                                                   let uu____10826
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid  in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu____10826
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10825
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10827 =
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
                                                          if uu____10827
                                                          then
                                                            let uu____10843 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10844 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10843,
                                                              uu____10844)
                                                          else
                                                            (let uu____10855
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10855))
                                                           in
                                                        (match uu____10791
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10879
                                                                 =
                                                                 let uu____10887
                                                                   =
                                                                   let uu____10888
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10889
                                                                    =
                                                                    let uu____10900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10900)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10888
                                                                    uu____10889
                                                                    in
                                                                 let uu____10909
                                                                   =
                                                                   let uu____10910
                                                                    =
                                                                    let uu____10912
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid  in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu____10912
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10910
                                                                    in
                                                                 (uu____10887,
                                                                   uu____10909,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10879
                                                                in
                                                             let uu____10918
                                                               =
                                                               let uu____10921
                                                                 =
                                                                 let uu____10924
                                                                   =
                                                                   let uu____10927
                                                                    =
                                                                    let uu____10930
                                                                    =
                                                                    let uu____10933
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10933
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10930
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10927
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10924
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10921
                                                                in
                                                             (uu____10918,
                                                               env2)))))))
                               | uu____10942 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____11002 =
                                   let uu____11008 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____11008,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____11002  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____11014 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11067  ->
                                         fun fvb  ->
                                           match uu____11067 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11122 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11122
                                                  in
                                               let gtok =
                                                 let uu____11126 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11126
                                                  in
                                               let env4 =
                                                 let uu____11129 =
                                                   let uu____11132 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun uu____11138  ->
                                                        FStar_Pervasives_Native.Some
                                                          uu____11138)
                                                     uu____11132
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11129
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____11014 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11258
                                     t_norm uu____11260 =
                                     match (uu____11258, uu____11260) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11290;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11291;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11293;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11294;_})
                                         ->
                                         let uu____11321 =
                                           let uu____11328 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11328 with
                                           | (tcenv',uu____11344,e_t) ->
                                               let uu____11350 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11361 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11350 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___748_11378 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___748_11378.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11321 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11391 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11391
                                                then
                                                  let uu____11396 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11398 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11400 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11396 uu____11398
                                                    uu____11400
                                                else ());
                                               (let uu____11405 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11405 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11432 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11432 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11454 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11454
                                                           then
                                                             let uu____11459
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11461
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11464
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11466
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11459
                                                               uu____11461
                                                               uu____11464
                                                               uu____11466
                                                           else ());
                                                          (let uu____11471 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11471
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11500)
                                                               ->
                                                               let uu____11513
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11526,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11530
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11530
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11543
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11543,
                                                                    decls0))
                                                                  in
                                                               (match uu____11513
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
                                                                    let uu____11564
                                                                    =
                                                                    let uu____11576
                                                                    =
                                                                    let uu____11579
                                                                    =
                                                                    let uu____11582
                                                                    =
                                                                    let uu____11585
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11585
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11582
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11579
                                                                     in
                                                                    (g,
                                                                    uu____11576,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11564
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
                                                                    let uu____11615
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11615
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
                                                                    let uu____11630
                                                                    =
                                                                    let uu____11633
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11633
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11630
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11639
                                                                    =
                                                                    let uu____11642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11642
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11639
                                                                     in
                                                                    let uu____11647
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11647
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11663
                                                                    =
                                                                    let uu____11671
                                                                    =
                                                                    let uu____11672
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11673
                                                                    =
                                                                    let uu____11689
                                                                    =
                                                                    let uu____11690
                                                                    =
                                                                    let uu____11695
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11695)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11690
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11689)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11672
                                                                    uu____11673
                                                                     in
                                                                    let uu____11709
                                                                    =
                                                                    let uu____11710
                                                                    =
                                                                    let uu____11712
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu____11712
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11710
                                                                     in
                                                                    (uu____11671,
                                                                    uu____11709,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11663
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11719
                                                                    =
                                                                    let uu____11727
                                                                    =
                                                                    let uu____11728
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11729
                                                                    =
                                                                    let uu____11740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11740)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11728
                                                                    uu____11729
                                                                     in
                                                                    (uu____11727,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11719
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11754
                                                                    =
                                                                    let uu____11762
                                                                    =
                                                                    let uu____11763
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11764
                                                                    =
                                                                    let uu____11775
                                                                    =
                                                                    let uu____11776
                                                                    =
                                                                    let uu____11781
                                                                    =
                                                                    let uu____11782
                                                                    =
                                                                    let uu____11785
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero
                                                                     in
                                                                    uu____11785
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11782
                                                                     in
                                                                    (gsapp,
                                                                    uu____11781)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11776
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11775)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11763
                                                                    uu____11764
                                                                     in
                                                                    (uu____11762,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11754
                                                                     in
                                                                    let uu____11799
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
                                                                    let uu____11811
                                                                    =
                                                                    let uu____11812
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11812
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11811
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu____11816
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11816
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11825
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11826
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu____11826
                                                                     in
                                                                    let uu____11828
                                                                    =
                                                                    let uu____11836
                                                                    =
                                                                    let uu____11837
                                                                    =
                                                                    let uu____11842
                                                                    =
                                                                    let uu____11843
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11844
                                                                    =
                                                                    let uu____11855
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11855)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11843
                                                                    uu____11844
                                                                     in
                                                                    (uu____11842,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11837
                                                                     in
                                                                    (uu____11836,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11828
                                                                     in
                                                                    let uu____11868
                                                                    =
                                                                    let uu____11877
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11877
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11892
                                                                    =
                                                                    let uu____11895
                                                                    =
                                                                    let uu____11896
                                                                    =
                                                                    let uu____11904
                                                                    =
                                                                    let uu____11905
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11906
                                                                    =
                                                                    let uu____11917
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11917)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11905
                                                                    uu____11906
                                                                     in
                                                                    (uu____11904,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11896
                                                                     in
                                                                    [uu____11895]
                                                                     in
                                                                    (d3,
                                                                    uu____11892)
                                                                     in
                                                                    match uu____11868
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11799
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11974
                                                                    =
                                                                    let uu____11977
                                                                    =
                                                                    let uu____11980
                                                                    =
                                                                    let uu____11983
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11983
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11980
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11977
                                                                     in
                                                                    let uu____11990
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11974,
                                                                    uu____11990,
                                                                    env02))))))))))
                                      in
                                   let uu____11995 =
                                     let uu____12008 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12071  ->
                                          fun uu____12072  ->
                                            match (uu____12071, uu____12072)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12197 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12197 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____12008
                                      in
                                   (match uu____11995 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12264 =
                                          let isDeclFun uu___1_12281 =
                                            match uu___1_12281 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12283 -> true
                                            | uu____12296 -> false  in
                                          let uu____12298 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12298
                                            (fun decls3  ->
                                               let uu____12328 =
                                                 FStar_List.fold_left
                                                   (fun uu____12359  ->
                                                      fun elt  ->
                                                        match uu____12359
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12400 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12400
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12428
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12428
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
                                                                    let uu___846_12466
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___846_12466.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___846_12466.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___846_12466.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12328 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12498 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12498, elts, rest))
                                           in
                                        (match uu____12264 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12527 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12533  ->
                                        match uu___2_12533 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12536 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12544 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12544)))
                                in
                             if uu____12527
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___863_12566  ->
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
                                      let uu____12611 = FStar_List.hd names
                                         in
                                      FStar_All.pipe_right uu____12611
                                        FStar_Pervasives_Native.snd
                                       in
                                    ((let uu____12629 =
                                        let uu____12639 =
                                          let uu____12647 =
                                            let uu____12649 =
                                              let uu____12651 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names
                                                 in
                                              FStar_All.pipe_right
                                                uu____12651
                                                (FStar_String.concat ",")
                                               in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12649
                                              (if plural
                                               then "their"
                                               else "its")
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12647, r)
                                           in
                                        [uu____12639]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12629);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12710 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12710
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12729 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12729, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12785 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12785 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l  in
      let uu____12791 = encode_sigelt' env se  in
      match uu____12791 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12803 =
                  let uu____12806 =
                    let uu____12807 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12807  in
                  [uu____12806]  in
                FStar_All.pipe_right uu____12803
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12812 ->
                let uu____12813 =
                  let uu____12816 =
                    let uu____12819 =
                      let uu____12820 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12820  in
                    [uu____12819]  in
                  FStar_All.pipe_right uu____12816
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12827 =
                  let uu____12830 =
                    let uu____12833 =
                      let uu____12836 =
                        let uu____12837 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12837  in
                      [uu____12836]  in
                    FStar_All.pipe_right uu____12833
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12830  in
                FStar_List.append uu____12813 uu____12827
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12851 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12851
       then
         let uu____12856 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12856
       else ());
      (let is_opaque_to_smt t =
         let uu____12868 =
           let uu____12869 = FStar_Syntax_Subst.compress t  in
           uu____12869.FStar_Syntax_Syntax.n  in
         match uu____12868 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12874)) -> s = "opaque_to_smt"
         | uu____12879 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12888 =
           let uu____12889 = FStar_Syntax_Subst.compress t  in
           uu____12889.FStar_Syntax_Syntax.n  in
         match uu____12888 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12894)) -> s = "uninterpreted_by_smt"
         | uu____12899 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____12905 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu____12917 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12935 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12936 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12949 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____12950 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12962 =
             let uu____12964 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12964  in
           if uu____12962
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12993 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         ((ed.FStar_Syntax_Syntax.binders), tm,
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))))
                      tm.FStar_Syntax_Syntax.pos
                 in
              let encode_action env1 a =
                let action_defn =
                  let uu____13026 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____13026  in
                let uu____13027 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____13027 with
                | (formals,uu____13039) ->
                    let arity = FStar_List.length formals  in
                    let uu____13047 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____13047 with
                     | (aname,atok,env2) ->
                         let uu____13069 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____13069 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____13085 =
                                  let uu____13086 =
                                    let uu____13098 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13118  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____13098,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____13086
                                   in
                                [uu____13085;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13135 =
                                let aux uu____13181 uu____13182 =
                                  match (uu____13181, uu____13182) with
                                  | ((bv,uu____13226),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13258 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13258 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13281 =
                                             let uu____13284 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13284 :: acc_sorts  in
                                           (env4, uu____13281, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13135 with
                               | (uu____13316,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13332 =
                                       let uu____13340 =
                                         let uu____13341 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13342 =
                                           let uu____13353 =
                                             let uu____13354 =
                                               let uu____13359 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13359)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13354
                                              in
                                           ([[app]], xs_sorts, uu____13353)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13341 uu____13342
                                          in
                                       (uu____13340,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13332
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13374 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13374
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13377 =
                                       let uu____13385 =
                                         let uu____13386 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13387 =
                                           let uu____13398 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13398)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13386 uu____13387
                                          in
                                       (uu____13385,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13377
                                      in
                                   let uu____13411 =
                                     let uu____13414 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13414  in
                                   (env2, uu____13411))))
                 in
              let uu____13423 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13423 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13449,uu____13450)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13451 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4))
              in
           (match uu____13451 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13473,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13480 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13486  ->
                       match uu___3_13486 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13489 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13495 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13498 -> false))
                in
             Prims.op_Negation uu____13480  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13508 =
                let uu____13513 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13513 env fv t quals  in
              match uu____13508 with
              | (decls,env1) ->
                  let tname = FStar_Ident.string_of_lid lid  in
                  let tsym =
                    let uu____13527 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13527  in
                  let uu____13530 =
                    let uu____13531 =
                      let uu____13534 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13534
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13531  in
                  (uu____13530, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13544 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13544 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1006_13556 = env  in
                  let uu____13557 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1006_13556.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1006_13556.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1006_13556.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13557;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1006_13556.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1006_13556.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1006_13556.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1006_13556.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1006_13556.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1006_13556.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1006_13556.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13559 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13559 with
                 | (f3,decls) ->
                     let g =
                       let uu____13573 =
                         let uu____13576 =
                           let uu____13577 =
                             let uu____13585 =
                               let uu____13586 =
                                 let uu____13588 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13588
                                  in
                               FStar_Pervasives_Native.Some uu____13586  in
                             let uu____13592 =
                               let uu____13594 =
                                 let uu____13596 =
                                   FStar_Ident.string_of_lid l  in
                                 Prims.op_Hat "assumption_" uu____13596  in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu____13594
                                in
                             (f3, uu____13585, uu____13592)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13577  in
                         [uu____13576]  in
                       FStar_All.pipe_right uu____13573
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13605) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13619 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13641 =
                        let uu____13644 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13644.FStar_Syntax_Syntax.fv_name  in
                      uu____13641.FStar_Syntax_Syntax.v  in
                    let uu____13645 =
                      let uu____13647 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13647  in
                    if uu____13645
                    then
                      let val_decl =
                        let uu___1023_13679 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1023_13679.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1023_13679.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1023_13679.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1023_13679.FStar_Syntax_Syntax.sigopts)
                        }  in
                      let uu____13680 = encode_sigelt' env1 val_decl  in
                      match uu____13680 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13619 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13716,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                           FStar_Syntax_Syntax.lbunivs = uu____13718;
                           FStar_Syntax_Syntax.lbtyp = uu____13719;
                           FStar_Syntax_Syntax.lbeff = uu____13720;
                           FStar_Syntax_Syntax.lbdef = uu____13721;
                           FStar_Syntax_Syntax.lbattrs = uu____13722;
                           FStar_Syntax_Syntax.lbpos = uu____13723;_}::[]),uu____13724)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu____13743 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one
              in
           (match uu____13743 with
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
                  let uu____13781 =
                    let uu____13784 =
                      let uu____13785 =
                        let uu____13793 =
                          let uu____13794 =
                            FStar_Syntax_Syntax.range_of_fv b2t  in
                          let uu____13795 =
                            let uu____13806 =
                              let uu____13807 =
                                let uu____13812 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13812)  in
                              FStar_SMTEncoding_Util.mkEq uu____13807  in
                            ([[b2t_x]], [xx], uu____13806)  in
                          FStar_SMTEncoding_Term.mkForall uu____13794
                            uu____13795
                           in
                        (uu____13793,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13785  in
                    [uu____13784]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13781
                   in
                let uu____13850 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13850, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13853,uu____13854) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13864  ->
                   match uu___4_13864 with
                   | FStar_Syntax_Syntax.Discriminator uu____13866 -> true
                   | uu____13868 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13870,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13882 =
                      let uu____13884 =
                        let uu____13885 = FStar_Ident.ns_of_lid l  in
                        FStar_List.hd uu____13885  in
                      FStar_Ident.string_of_id uu____13884  in
                    uu____13882 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13894  ->
                      match uu___5_13894 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13897 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13900) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13914  ->
                   match uu___6_13914 with
                   | FStar_Syntax_Syntax.Projector uu____13916 -> true
                   | uu____13922 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13926 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13926 with
            | FStar_Pervasives_Native.Some uu____13933 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1088_13935 = se  in
                  let uu____13936 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13936;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1088_13935.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1088_13935.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1088_13935.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1088_13935.FStar_Syntax_Syntax.sigopts)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13939) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1100_13960 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1100_13960.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1100_13960.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1100_13960.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1100_13960.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1100_13960.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13965) ->
           let uu____13974 = encode_sigelts env ses  in
           (match uu____13974 with
            | (g,env1) ->
                let uu____13985 =
                  FStar_List.fold_left
                    (fun uu____14009  ->
                       fun elt  ->
                         match uu____14009 with
                         | (g',inversions) ->
                             let uu____14037 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_14060  ->
                                       match uu___7_14060 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____14062;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____14063;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____14064;_}
                                           -> false
                                       | uu____14071 -> true))
                                in
                             (match uu____14037 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1126_14096 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1126_14096.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1126_14096.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1126_14096.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13985 with
                 | (g',inversions) ->
                     let uu____14115 =
                       FStar_List.fold_left
                         (fun uu____14146  ->
                            fun elt  ->
                              match uu____14146 with
                              | (decls,elts,rest) ->
                                  let uu____14187 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14196  ->
                                            match uu___8_14196 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14198 -> true
                                            | uu____14211 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14187
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14234 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14255  ->
                                               match uu___9_14255 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14257 -> true
                                               | uu____14270 -> false))
                                        in
                                     match uu____14234 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1148_14301 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1148_14301.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1148_14301.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1148_14301.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____14115 with
                      | (decls,elts,rest) ->
                          let uu____14327 =
                            let uu____14328 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14335 =
                              let uu____14338 =
                                let uu____14341 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14341  in
                              FStar_List.append elts uu____14338  in
                            FStar_List.append uu____14328 uu____14335  in
                          (uu____14327, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14352,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14365 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14365 with
             | (usubst,uvs) ->
                 let uu____14385 =
                   let uu____14392 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14393 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14394 =
                     let uu____14395 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14395 k  in
                   (uu____14392, uu____14393, uu____14394)  in
                 (match uu____14385 with
                  | (env1,tps1,k1) ->
                      let uu____14408 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14408 with
                       | (tps2,k2) ->
                           let uu____14416 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14416 with
                            | (uu____14424,k3) ->
                                let uu____14430 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14430 with
                                 | (tps3,env_tps,uu____14442,us) ->
                                     let u_k =
                                       let uu____14445 =
                                         let uu____14446 =
                                           FStar_Syntax_Syntax.fvar t
                                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                                Prims.int_zero)
                                             FStar_Pervasives_Native.None
                                            in
                                         let uu____14448 =
                                           let uu____14449 =
                                             FStar_Syntax_Util.args_of_binders
                                               tps3
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____14449
                                            in
                                         let uu____14454 =
                                           FStar_Ident.range_of_lid t  in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____14446 uu____14448
                                           uu____14454
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14445 k3
                                        in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14468) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14474,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14477) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  -> universe_leq u1 v))
                                       | (uu____14485,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14492) ->
                                           let uu____14493 =
                                             let uu____14495 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14495
                                              in
                                           failwith uu____14493
                                       | (uu____14499,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14500 =
                                             let uu____14502 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14502
                                              in
                                           failwith uu____14500
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14506,uu____14507) ->
                                           let uu____14518 =
                                             let uu____14520 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14520
                                              in
                                           failwith uu____14518
                                       | (uu____14524,FStar_Syntax_Syntax.U_unif
                                          uu____14525) ->
                                           let uu____14536 =
                                             let uu____14538 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14538
                                              in
                                           failwith uu____14536
                                       | uu____14542 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14555 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14555 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14573 = u_leq_u_k u_tp  in
                                       if uu____14573
                                       then true
                                       else
                                         (let uu____14580 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14580 with
                                          | (formals,uu____14589) ->
                                              let uu____14594 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14594 with
                                               | (uu____14604,uu____14605,uu____14606,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14617 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14617
             then
               let uu____14622 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14622
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14642  ->
                       match uu___10_14642 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14646 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14659 = c  in
                 match uu____14659 with
                 | (name,args,uu____14664,uu____14665,uu____14666) ->
                     let uu____14677 =
                       let uu____14678 =
                         let uu____14690 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14717  ->
                                   match uu____14717 with
                                   | (uu____14726,sort,uu____14728) -> sort))
                            in
                         (name, uu____14690,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14678  in
                     [uu____14677]
               else
                 (let uu____14739 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14739 c)
                in
             let inversion_axioms tapp vars =
               let uu____14757 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14765 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14765 FStar_Option.isNone))
                  in
               if uu____14757
               then []
               else
                 (let uu____14800 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14800 with
                  | (xxsym,xx) ->
                      let uu____14813 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14852  ->
                                fun l  ->
                                  match uu____14852 with
                                  | (out,decls) ->
                                      let uu____14872 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14872 with
                                       | (uu____14883,data_t) ->
                                           let uu____14885 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14885 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14905 =
                                                    let uu____14906 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14906.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14905 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14909,indices)
                                                      -> indices
                                                  | uu____14935 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____14965  ->
                                                            match uu____14965
                                                            with
                                                            | (x,uu____14973)
                                                                ->
                                                                let uu____14978
                                                                  =
                                                                  let uu____14979
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____14987,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____14979
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____14978)
                                                       env)
                                                   in
                                                let uu____14992 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____14992 with
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
                                                                  let uu____15027
                                                                    =
                                                                    let uu____15032
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    (uu____15032,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____15027)
                                                             vars indices1
                                                         else []  in
                                                       let uu____15035 =
                                                         let uu____15036 =
                                                           let uu____15041 =
                                                             let uu____15042
                                                               =
                                                               let uu____15047
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____15048
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____15047,
                                                                 uu____15048)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____15042
                                                              in
                                                           (out, uu____15041)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____15036
                                                          in
                                                       (uu____15035,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14813 with
                       | (data_ax,decls) ->
                           let uu____15063 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____15063 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu____15080 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____15080 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____15087 =
                                    let uu____15095 =
                                      let uu____15096 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15097 =
                                        let uu____15108 =
                                          let uu____15109 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15111 =
                                            let uu____15114 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15114 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15109 uu____15111
                                           in
                                        let uu____15116 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15108,
                                          uu____15116)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15096 uu____15097
                                       in
                                    let uu____15125 =
                                      let uu____15127 =
                                        let uu____15129 =
                                          FStar_Ident.string_of_lid t  in
                                        Prims.op_Hat
                                          "fuel_guarded_inversion_"
                                          uu____15129
                                         in
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        uu____15127
                                       in
                                    (uu____15095,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15125)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____15087
                                   in
                                let uu____15135 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15135)))
                in
             let uu____15142 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15156 ->
                     let uu____15157 =
                       let uu____15158 =
                         let uu____15173 = FStar_Syntax_Syntax.mk_Total k  in
                         (tps, uu____15173)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15158  in
                     FStar_Syntax_Syntax.mk uu____15157
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15142 with
             | (formals,res) ->
                 let uu____15197 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15197 with
                  | (vars,guards,env',binder_decls,uu____15222) ->
                      let arity = FStar_List.length vars  in
                      let uu____15236 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15236 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15262 =
                               let uu____15270 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15270)  in
                             FStar_SMTEncoding_Util.mkApp uu____15262  in
                           let uu____15276 =
                             let tname_decl =
                               let uu____15286 =
                                 let uu____15287 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15306 =
                                             let uu____15308 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15308
                                              in
                                           let uu____15310 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15306, uu____15310, false)))
                                    in
                                 let uu____15314 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15287,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15314, false)
                                  in
                               constructor_or_logic_type_decl uu____15286  in
                             let uu____15322 =
                               match vars with
                               | [] ->
                                   let uu____15335 =
                                     let uu____15336 =
                                       let uu____15339 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____15345  ->
                                            FStar_Pervasives_Native.Some
                                              uu____15345) uu____15339
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15336
                                      in
                                   ([], uu____15335)
                               | uu____15348 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15358 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15358
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15374 =
                                       let uu____15382 =
                                         let uu____15383 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15384 =
                                           let uu____15400 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15400)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15383 uu____15384
                                          in
                                       (uu____15382,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15374
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15322 with
                             | (tok_decls,env2) ->
                                 let uu____15427 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15427
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15276 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15455 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15455 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____15477 =
                                            let uu____15478 =
                                              let uu____15486 =
                                                let uu____15487 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15487
                                                 in
                                              (uu____15486,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15478
                                             in
                                          [uu____15477]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15497 =
                                          FStar_List.map
                                            (fun uu____15501  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15497 true
                                         in
                                      let uu____15503 =
                                        let uu____15506 =
                                          let uu____15509 =
                                            let uu____15512 =
                                              let uu____15513 =
                                                let uu____15521 =
                                                  let uu____15522 =
                                                    let uu____15527 =
                                                      let uu____15528 =
                                                        let uu____15539 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15539)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15528
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15527)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15522
                                                   in
                                                (uu____15521,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15513
                                               in
                                            [uu____15512]  in
                                          FStar_List.append karr uu____15509
                                           in
                                        FStar_All.pipe_right uu____15506
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15503
                                   in
                                let aux =
                                  let uu____15558 =
                                    let uu____15561 =
                                      inversion_axioms tapp vars  in
                                    let uu____15564 =
                                      let uu____15567 =
                                        let uu____15570 =
                                          let uu____15571 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15571 env2 tapp
                                            vars
                                           in
                                        [uu____15570]  in
                                      FStar_All.pipe_right uu____15567
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15561 uu____15564
                                     in
                                  FStar_List.append kindingAx uu____15558  in
                                let g =
                                  let uu____15579 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15579
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15587,uu____15588,uu____15589,uu____15590,uu____15591)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15599,t,uu____15601,n_tps,uu____15603) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15614 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15614 with
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
                           | (vars,guards,env',binder_decls,names) ->
                               let fields =
                                 FStar_All.pipe_right names
                                   (FStar_List.mapi
                                      (fun n  ->
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
                                                    let uu____16004 =
                                                      let uu____16005 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16005
                                                       in
                                                    [uu____16004]
                                                 in
                                              let encode_elim uu____16021 =
                                                let uu____16022 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16022 with
                                                | (head,args) ->
                                                    let uu____16073 =
                                                      let uu____16074 =
                                                        FStar_Syntax_Subst.compress
                                                          head
                                                         in
                                                      uu____16074.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16073 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16086;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16087;_},uu____16088)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16094 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16094
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
                                                                  | uu____16157
                                                                    ->
                                                                    let uu____16158
                                                                    =
                                                                    let uu____16164
                                                                    =
                                                                    let uu____16166
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16166
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16164)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16158
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16189
                                                                    =
                                                                    let uu____16191
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16191
                                                                     in
                                                                    if
                                                                    uu____16189
                                                                    then
                                                                    let uu____16213
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16213]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16216
                                                                =
                                                                let uu____16230
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16287
                                                                     ->
                                                                    fun
                                                                    uu____16288
                                                                     ->
                                                                    match 
                                                                    (uu____16287,
                                                                    uu____16288)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16399
                                                                    =
                                                                    let uu____16407
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16407
                                                                     in
                                                                    (match uu____16399
                                                                    with
                                                                    | 
                                                                    (uu____16421,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16432
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16432
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16437
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16437
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
                                                                  uu____16230
                                                                 in
                                                              (match uu____16216
                                                               with
                                                               | (uu____16458,arg_vars,elim_eqns_or_guards,uu____16461)
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
                                                                    let uu____16488
                                                                    =
                                                                    let uu____16496
                                                                    =
                                                                    let uu____16497
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16498
                                                                    =
                                                                    let uu____16509
                                                                    =
                                                                    let uu____16510
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16510
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16512
                                                                    =
                                                                    let uu____16513
                                                                    =
                                                                    let uu____16518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16518)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16513
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16509,
                                                                    uu____16512)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16497
                                                                    uu____16498
                                                                     in
                                                                    (uu____16496,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16488
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____16533
                                                                    =
                                                                    let uu____16534
                                                                    =
                                                                    let uu____16540
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16540,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16534
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16533
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____16546
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
                                                                    (let uu____16569
                                                                    =
                                                                    let uu____16570
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____16570
                                                                    dapp1  in
                                                                    [uu____16569])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16546
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16577
                                                                    =
                                                                    let uu____16585
                                                                    =
                                                                    let uu____16586
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16587
                                                                    =
                                                                    let uu____16598
                                                                    =
                                                                    let uu____16599
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16599
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16601
                                                                    =
                                                                    let uu____16602
                                                                    =
                                                                    let uu____16607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16607)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16602
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16598,
                                                                    uu____16601)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16586
                                                                    uu____16587
                                                                     in
                                                                    (uu____16585,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16577
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
                                                         let uu____16626 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16626
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
                                                                  | uu____16689
                                                                    ->
                                                                    let uu____16690
                                                                    =
                                                                    let uu____16696
                                                                    =
                                                                    let uu____16698
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16698
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16696)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16690
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16721
                                                                    =
                                                                    let uu____16723
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16723
                                                                     in
                                                                    if
                                                                    uu____16721
                                                                    then
                                                                    let uu____16745
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16745]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16748
                                                                =
                                                                let uu____16762
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16819
                                                                     ->
                                                                    fun
                                                                    uu____16820
                                                                     ->
                                                                    match 
                                                                    (uu____16819,
                                                                    uu____16820)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16931
                                                                    =
                                                                    let uu____16939
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16939
                                                                     in
                                                                    (match uu____16931
                                                                    with
                                                                    | 
                                                                    (uu____16953,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16964
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16964
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16969
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
                                                                  uu____16762
                                                                 in
                                                              (match uu____16748
                                                               with
                                                               | (uu____16990,arg_vars,elim_eqns_or_guards,uu____16993)
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
                                                                    let uu____17020
                                                                    =
                                                                    let uu____17028
                                                                    =
                                                                    let uu____17029
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17030
                                                                    =
                                                                    let uu____17041
                                                                    =
                                                                    let uu____17042
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17042
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17044
                                                                    =
                                                                    let uu____17045
                                                                    =
                                                                    let uu____17050
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17050)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17045
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17041,
                                                                    uu____17044)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17029
                                                                    uu____17030
                                                                     in
                                                                    (uu____17028,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17020
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____17065
                                                                    =
                                                                    let uu____17066
                                                                    =
                                                                    let uu____17072
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17072,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17066
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17065
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____17078
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
                                                                    (let uu____17101
                                                                    =
                                                                    let uu____17102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____17102
                                                                    dapp1  in
                                                                    [uu____17101])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17078
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17109
                                                                    =
                                                                    let uu____17117
                                                                    =
                                                                    let uu____17118
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17119
                                                                    =
                                                                    let uu____17130
                                                                    =
                                                                    let uu____17131
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17131
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17133
                                                                    =
                                                                    let uu____17134
                                                                    =
                                                                    let uu____17139
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17139)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17134
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17130,
                                                                    uu____17133)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17118
                                                                    uu____17119
                                                                     in
                                                                    (uu____17117,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17109
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17156 ->
                                                         ((let uu____17158 =
                                                             let uu____17164
                                                               =
                                                               let uu____17166
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17168
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17166
                                                                 uu____17168
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17164)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17158);
                                                          ([], [])))
                                                 in
                                              let uu____17176 =
                                                encode_elim ()  in
                                              (match uu____17176 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17202 =
                                                       let uu____17205 =
                                                         let uu____17208 =
                                                           let uu____17211 =
                                                             let uu____17214
                                                               =
                                                               let uu____17217
                                                                 =
                                                                 let uu____17220
                                                                   =
                                                                   let uu____17221
                                                                    =
                                                                    let uu____17233
                                                                    =
                                                                    let uu____17234
                                                                    =
                                                                    let uu____17236
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17236
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17234
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17233)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17221
                                                                    in
                                                                 [uu____17220]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17217
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17214
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17247 =
                                                             let uu____17250
                                                               =
                                                               let uu____17253
                                                                 =
                                                                 let uu____17256
                                                                   =
                                                                   let uu____17259
                                                                    =
                                                                    let uu____17262
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17267
                                                                    =
                                                                    let uu____17270
                                                                    =
                                                                    let uu____17271
                                                                    =
                                                                    let uu____17279
                                                                    =
                                                                    let uu____17280
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17281
                                                                    =
                                                                    let uu____17292
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17292)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17280
                                                                    uu____17281
                                                                     in
                                                                    (uu____17279,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17271
                                                                     in
                                                                    let uu____17305
                                                                    =
                                                                    let uu____17308
                                                                    =
                                                                    let uu____17309
                                                                    =
                                                                    let uu____17317
                                                                    =
                                                                    let uu____17318
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17319
                                                                    =
                                                                    let uu____17330
                                                                    =
                                                                    let uu____17331
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17331
                                                                    vars'  in
                                                                    let uu____17333
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17330,
                                                                    uu____17333)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17318
                                                                    uu____17319
                                                                     in
                                                                    (uu____17317,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17309
                                                                     in
                                                                    [uu____17308]
                                                                     in
                                                                    uu____17270
                                                                    ::
                                                                    uu____17305
                                                                     in
                                                                    uu____17262
                                                                    ::
                                                                    uu____17267
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17259
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17256
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17253
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17250
                                                              in
                                                           FStar_List.append
                                                             uu____17211
                                                             uu____17247
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17208
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17205
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17202
                                                      in
                                                   let uu____17350 =
                                                     let uu____17351 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17351 g
                                                      in
                                                   (uu____17350, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17385  ->
              fun se  ->
                match uu____17385 with
                | (g,env1) ->
                    let uu____17405 = encode_sigelt env1 se  in
                    (match uu____17405 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17473 =
        match uu____17473 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17510 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17518 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17518
                   then
                     let uu____17523 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17525 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17527 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17523 uu____17525 uu____17527
                   else ());
                  (let uu____17532 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17532 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17550 =
                         let uu____17558 =
                           let uu____17560 =
                             let uu____17562 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17562
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17560  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17558
                          in
                       (match uu____17550 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17582 = FStar_Options.log_queries ()
                                 in
                              if uu____17582
                              then
                                let uu____17585 =
                                  let uu____17587 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17589 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17591 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17587 uu____17589 uu____17591
                                   in
                                FStar_Pervasives_Native.Some uu____17585
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17607 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17617 =
                                let uu____17620 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17620  in
                              FStar_List.append uu____17607 uu____17617  in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17632,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17652 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17652 with
                  | (g,env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env')))
         in
      let uu____17673 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env)
         in
      match uu____17673 with | (uu____17700,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17753  ->
              match uu____17753 with
              | (l,uu____17762,uu____17763) ->
                  let uu____17766 =
                    let uu____17778 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17778, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17766))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17811  ->
              match uu____17811 with
              | (l,uu____17822,uu____17823) ->
                  let uu____17826 =
                    let uu____17827 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun uu____17830  ->
                         FStar_SMTEncoding_Term.Echo uu____17830) uu____17827
                     in
                  let uu____17831 =
                    let uu____17834 =
                      let uu____17835 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17835  in
                    [uu____17834]  in
                  uu____17826 :: uu____17831))
       in
    (prefix, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17853 =
      let uu____17856 =
        let uu____17857 = FStar_Util.psmap_empty ()  in
        let uu____17872 =
          let uu____17881 = FStar_Util.psmap_empty ()  in (uu____17881, [])
           in
        let uu____17888 =
          let uu____17890 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17890 FStar_Ident.string_of_lid  in
        let uu____17892 = FStar_Util.smap_create (Prims.of_int (100))  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17857;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17872;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17888;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17892
        }  in
      [uu____17856]  in
    FStar_ST.op_Colon_Equals last_env uu____17853
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17936 = FStar_ST.op_Bang last_env  in
      match uu____17936 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17964 ->
          let uu___1572_17967 = e  in
          let uu____17968 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1572_17967.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1572_17967.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1572_17967.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1572_17967.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1572_17967.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1572_17967.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1572_17967.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17968;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1572_17967.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1572_17967.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____17976 = FStar_ST.op_Bang last_env  in
    match uu____17976 with
    | [] -> failwith "Empty env stack"
    | uu____18003::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
  
let (push_env : unit -> unit) =
  fun uu____18035  ->
    let uu____18036 = FStar_ST.op_Bang last_env  in
    match uu____18036 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd  in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
  
let (pop_env : unit -> unit) =
  fun uu____18096  ->
    let uu____18097 = FStar_ST.op_Bang last_env  in
    match uu____18097 with
    | [] -> failwith "Popping an empty stack"
    | uu____18124::tl -> FStar_ST.op_Colon_Equals last_env tl
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18161  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18214  ->
         let uu____18215 = snapshot_env ()  in
         match uu____18215 with
         | (env_depth,()) ->
             let uu____18237 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18237 with
              | (varops_depth,()) ->
                  let uu____18259 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18259 with
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
        (fun uu____18317  ->
           let uu____18318 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18318 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18413 = snapshot msg  in () 
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
        | (uu____18459::uu____18460,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1633_18468 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1633_18468.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1633_18468.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1633_18468.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18469 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1639_18496 = elt  in
        let uu____18497 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1639_18496.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1639_18496.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18497;
          FStar_SMTEncoding_Term.a_names =
            (uu___1639_18496.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18517 =
        let uu____18520 =
          let uu____18521 =
            let uu____18522 = FStar_Ident.ns_of_lid lid  in
            FStar_Ident.lid_of_ids uu____18522  in
          FStar_SMTEncoding_Term.Namespace uu____18521  in
        let uu____18523 = open_fact_db_tags env  in uu____18520 ::
          uu____18523
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18517
  
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
      let uu____18550 = encode_sigelt env se  in
      match uu____18550 with
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
                (let uu____18596 =
                   let uu____18599 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18599
                    in
                 match uu____18596 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18614 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18614
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18644 = FStar_Options.log_queries ()  in
        if uu____18644
        then
          let uu____18649 =
            let uu____18650 =
              let uu____18652 =
                let uu____18654 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18654 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18652  in
            FStar_SMTEncoding_Term.Caption uu____18650  in
          uu____18649 :: decls
        else decls  in
      (let uu____18673 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18673
       then
         let uu____18676 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18676
       else ());
      (let env =
         let uu____18682 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18682 tcenv  in
       let uu____18683 = encode_top_level_facts env se  in
       match uu____18683 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18697 =
               let uu____18700 =
                 let uu____18703 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18703
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18700  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18697)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18736 = FStar_Options.log_queries ()  in
          if uu____18736
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1677_18756 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1677_18756.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1677_18756.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1677_18756.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1677_18756.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1677_18756.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1677_18756.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1677_18756.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1677_18756.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1677_18756.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1677_18756.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18761 =
             let uu____18764 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18764
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18761  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18784 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18784
      then ([], [])
      else
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____18817  ->
             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh
               ();
             (let name =
                let uu____18821 =
                  FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format2 "%s %s"
                  (if modul.FStar_Syntax_Syntax.is_interface
                   then "interface"
                   else "module") uu____18821
                 in
              (let uu____18831 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____18831
               then
                 let uu____18834 =
                   FStar_All.pipe_right
                     (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                     Prims.string_of_int
                    in
                 FStar_Util.print2
                   "+++++++++++Encoding externals for %s ... %s exports\n"
                   name uu____18834
               else ());
              (let env =
                 let uu____18842 =
                   get_env modul.FStar_Syntax_Syntax.name tcenv  in
                 FStar_All.pipe_right uu____18842
                   FStar_SMTEncoding_Env.reset_current_module_fvbs
                  in
               let encode_signature env1 ses =
                 FStar_All.pipe_right ses
                   (FStar_List.fold_left
                      (fun uu____18881  ->
                         fun se  ->
                           match uu____18881 with
                           | (g,env2) ->
                               let uu____18901 =
                                 encode_top_level_facts env2 se  in
                               (match uu____18901 with
                                | (g',env3) ->
                                    ((FStar_List.append g g'), env3)))
                      ([], env1))
                  in
               let uu____18924 =
                 encode_signature
                   (let uu___1701_18933 = env  in
                    {
                      FStar_SMTEncoding_Env.bvar_bindings =
                        (uu___1701_18933.FStar_SMTEncoding_Env.bvar_bindings);
                      FStar_SMTEncoding_Env.fvar_bindings =
                        (uu___1701_18933.FStar_SMTEncoding_Env.fvar_bindings);
                      FStar_SMTEncoding_Env.depth =
                        (uu___1701_18933.FStar_SMTEncoding_Env.depth);
                      FStar_SMTEncoding_Env.tcenv =
                        (uu___1701_18933.FStar_SMTEncoding_Env.tcenv);
                      FStar_SMTEncoding_Env.warn = false;
                      FStar_SMTEncoding_Env.nolabels =
                        (uu___1701_18933.FStar_SMTEncoding_Env.nolabels);
                      FStar_SMTEncoding_Env.use_zfuel_name =
                        (uu___1701_18933.FStar_SMTEncoding_Env.use_zfuel_name);
                      FStar_SMTEncoding_Env.encode_non_total_function_typ =
                        (uu___1701_18933.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                      FStar_SMTEncoding_Env.current_module_name =
                        (uu___1701_18933.FStar_SMTEncoding_Env.current_module_name);
                      FStar_SMTEncoding_Env.encoding_quantifier =
                        (uu___1701_18933.FStar_SMTEncoding_Env.encoding_quantifier);
                      FStar_SMTEncoding_Env.global_cache =
                        (uu___1701_18933.FStar_SMTEncoding_Env.global_cache)
                    }) modul.FStar_Syntax_Syntax.exports
                  in
               match uu____18924 with
               | (decls,env1) ->
                   (give_decls_to_z3_and_set_env env1 name decls;
                    (let uu____18951 =
                       FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium
                        in
                     if uu____18951
                     then
                       FStar_Util.print1 "Done encoding externals for %s\n"
                         name
                     else ());
                    (let uu____18957 =
                       FStar_All.pipe_right env1
                         FStar_SMTEncoding_Env.get_current_module_fvbs
                        in
                     (decls, uu____18957))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun tcmod  ->
      fun uu____18987  ->
        match uu____18987 with
        | (decls,fvbs) ->
            let uu____19000 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
            if uu____19000
            then ()
            else
              (let name =
                 let uu____19007 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name
                    in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu____19007
                  in
               (let uu____19017 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____19017
                then
                  let uu____19020 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int
                     in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19020
                else ());
               (let env =
                  let uu____19028 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv  in
                  FStar_All.pipe_right uu____19028
                    FStar_SMTEncoding_Env.reset_current_module_fvbs
                   in
                let env1 =
                  let uu____19030 = FStar_All.pipe_right fvbs FStar_List.rev
                     in
                  FStar_All.pipe_right uu____19030
                    (FStar_List.fold_left
                       (fun env1  ->
                          fun fvb  ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env)
                   in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19044 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19044
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
        (let uu____19106 =
           let uu____19108 = FStar_TypeChecker_Env.current_module tcenv  in
           FStar_Ident.string_of_lid uu____19108  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19106);
        (let env =
           let uu____19110 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19110 tcenv  in
         let uu____19111 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19148 = aux rest  in
                 (match uu____19148 with
                  | (out,rest1) ->
                      let t =
                        let uu____19176 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19176 with
                        | FStar_Pervasives_Native.Some uu____19179 ->
                            let uu____19180 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19180
                              x.FStar_Syntax_Syntax.sort
                        | uu____19181 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        norm_with_steps
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19185 =
                        let uu____19188 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1744_19191 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1744_19191.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1744_19191.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19188 :: out  in
                      (uu____19185, rest1))
             | uu____19196 -> ([], bindings)  in
           let uu____19203 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19203 with
           | (closing,bindings) ->
               let uu____19228 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19228, bindings)
            in
         match uu____19111 with
         | (q1,bindings) ->
             let uu____19251 = encode_env_bindings env bindings  in
             (match uu____19251 with
              | (env_decls,env1) ->
                  ((let uu____19273 =
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
                    if uu____19273
                    then
                      let uu____19280 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula {: %s\n"
                        uu____19280
                    else ());
                   (let uu____19285 =
                      FStar_Util.record_time
                        (fun uu____19300  ->
                           FStar_SMTEncoding_EncodeTerm.encode_formula q1
                             env1)
                       in
                    match uu____19285 with
                    | ((phi,qdecls),ms) ->
                        let uu____19324 =
                          let uu____19329 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19329 phi
                           in
                        (match uu____19324 with
                         | (labels,phi1) ->
                             let uu____19346 = encode_labels labels  in
                             (match uu____19346 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19382 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19382
                                    then
                                      let uu____19387 =
                                        let uu____19388 =
                                          let uu____19390 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula : "
                                            uu____19390
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19388
                                         in
                                      [uu____19387]
                                    else []  in
                                  let query_prelude =
                                    let uu____19398 =
                                      let uu____19399 =
                                        let uu____19400 =
                                          let uu____19403 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19410 =
                                            let uu____19413 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19413
                                             in
                                          FStar_List.append uu____19403
                                            uu____19410
                                           in
                                        FStar_List.append env_decls
                                          uu____19400
                                         in
                                      FStar_All.pipe_right uu____19399
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19398
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19423 =
                                      let uu____19431 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19432 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19431,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19432)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19423
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  ((let uu____19445 =
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
                                    if uu____19445
                                    then
                                      FStar_Util.print_string
                                        "} Done encoding\n"
                                    else ());
                                   (let uu____19456 =
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
                                    if uu____19456
                                    then
                                      FStar_Util.print1
                                        "Encoding took %sms\n"
                                        (Prims.string_of_int ms)
                                    else ());
                                   (query_prelude, labels, qry, suffix))))))))
  