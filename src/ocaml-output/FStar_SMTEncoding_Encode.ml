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
  = fun projectee  -> match projectee with | { mk = mk1; is;_} -> mk1 
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  -> match projectee with | { mk = mk1; is;_} -> is 
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
                let prims1 =
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
                let mk1 l v1 =
                  let uu____3566 =
                    let uu____3578 =
                      FStar_All.pipe_right prims1
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
                                b uu____3850 v1))
                     in
                  FStar_All.pipe_right uu____3566 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____3933  ->
                          match uu____3933 with
                          | (l',uu____3954) -> FStar_Ident.lid_equals l l'))
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
  let mkForall_fuel1 env =
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
              let uu____4319 = mkForall_fuel1 env  in uu____4319 uu____4318
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
              let uu____4500 = mkForall_fuel1 env  in uu____4500 uu____4499
               in
            uu____4484 uu____4440  in
          (uu____4439, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4431  in
      [uu____4430]  in
    uu____4366 :: uu____4427  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____4543 =
        let uu____4544 =
          let uu____4550 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
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
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
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
              let uu____4703 = mkForall_fuel1 env  in uu____4703 uu____4702
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
                let uu____4845 = mkForall_fuel1 env  in uu____4845 uu____4844
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
    let lex_t1 =
      let uu____4888 =
        let uu____4889 =
          let uu____4895 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
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
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
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
              let uu____5050 = mkForall_fuel1 env  in uu____5050 uu____5049
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
                let uu____5192 = mkForall_fuel1 env  in uu____5192 uu____5191
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
              let uu____5373 = mkForall_fuel1 env  in uu____5373 uu____5372
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
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.op_Hat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.op_Hat "lemma_" lid.FStar_Ident.str))
                   in
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
              let uu____7269 =
                ((let uu____7273 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____7273) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____7269
              then
                let arg_sorts =
                  let uu____7285 =
                    let uu____7286 = FStar_Syntax_Subst.compress t_norm  in
                    uu____7286.FStar_Syntax_Syntax.n  in
                  match uu____7285 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7292) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____7330  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____7337 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____7339 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____7339 with
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
                    let uu____7371 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____7371, env1)
              else
                (let uu____7376 = prims.is lid  in
                 if uu____7376
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____7385 = prims.mk lid vname  in
                   match uu____7385 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____7409 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____7409, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____7418 =
                      let uu____7437 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7437 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7465 =
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7465
                            then
                              let uu____7470 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___316_7473 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___316_7473.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___316_7473.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___316_7473.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___316_7473.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___316_7473.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___316_7473.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___316_7473.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___316_7473.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___316_7473.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___316_7473.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___316_7473.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___316_7473.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___316_7473.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___316_7473.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___316_7473.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___316_7473.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___316_7473.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___316_7473.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___316_7473.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___316_7473.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___316_7473.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___316_7473.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___316_7473.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___316_7473.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___316_7473.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___316_7473.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___316_7473.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___316_7473.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___316_7473.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___316_7473.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___316_7473.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___316_7473.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___316_7473.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___316_7473.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___316_7473.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___316_7473.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___316_7473.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___316_7473.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___316_7473.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___316_7473.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___316_7473.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___316_7473.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___316_7473.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___316_7473.FStar_TypeChecker_Env.erasable_types_tab)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7470
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7496 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____7496)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____7418 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7602  ->
                                  match uu___0_7602 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7606 = FStar_Util.prefix vars
                                         in
                                      (match uu____7606 with
                                       | (uu____7639,xxv) ->
                                           let xx =
                                             let uu____7678 =
                                               let uu____7679 =
                                                 let uu____7685 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7685,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7679
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7678
                                              in
                                           let uu____7688 =
                                             let uu____7689 =
                                               let uu____7697 =
                                                 let uu____7698 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7699 =
                                                   let uu____7710 =
                                                     let uu____7711 =
                                                       let uu____7716 =
                                                         let uu____7717 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7717
                                                          in
                                                       (vapp, uu____7716)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7711
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7710)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7698 uu____7699
                                                  in
                                               (uu____7697,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.op_Hat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7689
                                              in
                                           [uu____7688])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7732 = FStar_Util.prefix vars
                                         in
                                      (match uu____7732 with
                                       | (uu____7765,xxv) ->
                                           let xx =
                                             let uu____7804 =
                                               let uu____7805 =
                                                 let uu____7811 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7811,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7805
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7804
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
                                           let uu____7822 =
                                             let uu____7823 =
                                               let uu____7831 =
                                                 let uu____7832 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7833 =
                                                   let uu____7844 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7844)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7832 uu____7833
                                                  in
                                               (uu____7831,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7823
                                              in
                                           [uu____7822])
                                  | uu____7857 -> []))
                           in
                        let uu____7858 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7858 with
                         | (vars,guards,env',decls1,uu____7883) ->
                             let uu____7896 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7909 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7909, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7913 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7913 with
                                    | (g,ds) ->
                                        let uu____7926 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7926,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7896 with
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
                                  let should_thunk uu____7949 =
                                    let is_type1 t =
                                      let uu____7957 =
                                        let uu____7958 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____7958.FStar_Syntax_Syntax.n  in
                                      match uu____7957 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____7962 -> true
                                      | uu____7964 -> false  in
                                    let is_squash1 t =
                                      let uu____7973 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____7973 with
                                      | (head1,uu____7992) ->
                                          let uu____8017 =
                                            let uu____8018 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____8018.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____8017 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____8023;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____8024;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____8026;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____8027;_};_},uu____8028)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____8036 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____8041 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____8041))
                                       &&
                                       (let uu____8047 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____8047))
                                      &&
                                      (let uu____8050 = is_type1 t_norm  in
                                       Prims.op_Negation uu____8050)
                                     in
                                  let uu____8052 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____8111 -> (false, vars)  in
                                  (match uu____8052 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____8161 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____8161 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____8193 =
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
                                              | uu____8214 ->
                                                  let uu____8223 =
                                                    let uu____8231 =
                                                      get_vtok ()  in
                                                    (uu____8231, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8223
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____8238 =
                                                let uu____8246 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____8246)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____8238
                                               in
                                            let uu____8260 =
                                              let vname_decl =
                                                let uu____8268 =
                                                  let uu____8280 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____8280,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____8268
                                                 in
                                              let uu____8291 =
                                                let env2 =
                                                  let uu___411_8297 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___411_8297.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____8298 =
                                                  let uu____8300 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____8300
                                                   in
                                                if uu____8298
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____8291 with
                                              | (tok_typing,decls2) ->
                                                  let uu____8317 =
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
                                                        let uu____8343 =
                                                          let uu____8346 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8346
                                                           in
                                                        let uu____8353 =
                                                          let uu____8354 =
                                                            let uu____8357 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _8363  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _8363)
                                                              uu____8357
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____8354
                                                           in
                                                        (uu____8343,
                                                          uu____8353)
                                                    | uu____8366 when thunked
                                                        -> (decls2, env1)
                                                    | uu____8379 ->
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
                                                          let uu____8403 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8404 =
                                                            let uu____8415 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8415)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8403
                                                            uu____8404
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8425 =
                                                            let uu____8433 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8433,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8425
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
                                                            let uu____8444 =
                                                              let uu____8445
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8445]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8444
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8472 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8473 =
                                                              let uu____8484
                                                                =
                                                                let uu____8485
                                                                  =
                                                                  let uu____8490
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8491
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8490,
                                                                    uu____8491)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8485
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8484)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8472
                                                              uu____8473
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8520 =
                                                          let uu____8523 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8523
                                                           in
                                                        (uu____8520, env1)
                                                     in
                                                  (match uu____8317 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8544 =
                                                         let uu____8547 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8547
                                                           tok_decl
                                                          in
                                                       (uu____8544, env2))
                                               in
                                            (match uu____8260 with
                                             | (decls2,env2) ->
                                                 let uu____8566 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8576 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8576 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8591 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8591, decls)
                                                    in
                                                 (match uu____8566 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8606 =
                                                          let uu____8614 =
                                                            let uu____8615 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8616 =
                                                              let uu____8627
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8627)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8615
                                                              uu____8616
                                                             in
                                                          (uu____8614,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8606
                                                         in
                                                      let freshness =
                                                        let uu____8643 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8643
                                                        then
                                                          let uu____8651 =
                                                            let uu____8652 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8653 =
                                                              let uu____8666
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8673
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8666,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8673)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8652
                                                              uu____8653
                                                             in
                                                          let uu____8679 =
                                                            let uu____8682 =
                                                              let uu____8683
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8683
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8682]  in
                                                          uu____8651 ::
                                                            uu____8679
                                                        else []  in
                                                      let g =
                                                        let uu____8689 =
                                                          let uu____8692 =
                                                            let uu____8695 =
                                                              let uu____8698
                                                                =
                                                                let uu____8701
                                                                  =
                                                                  let uu____8704
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8704
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8701
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8698
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8695
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8692
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8689
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
          let uu____8744 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8744 with
          | FStar_Pervasives_Native.None  ->
              let uu____8755 = encode_free_var false env x t t_norm []  in
              (match uu____8755 with
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
            let uu____8818 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8818 with
            | (decls,env1) ->
                let uu____8829 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8829
                then
                  let uu____8836 =
                    let uu____8837 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8837  in
                  (uu____8836, env1)
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
             (fun uu____8893  ->
                fun lb  ->
                  match uu____8893 with
                  | (decls,env1) ->
                      let uu____8913 =
                        let uu____8918 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8918
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8913 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____8947 = FStar_Syntax_Util.head_and_args t  in
    match uu____8947 with
    | (hd1,args) ->
        let uu____8991 =
          let uu____8992 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8992.FStar_Syntax_Syntax.n  in
        (match uu____8991 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____8998,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____9022 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____9033 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___495_9041 = en  in
    let uu____9042 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___495_9041.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___495_9041.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___495_9041.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___495_9041.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___495_9041.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___495_9041.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___495_9041.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___495_9041.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___495_9041.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___495_9041.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9042
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____9072  ->
      fun quals  ->
        match uu____9072 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____9177 = FStar_Util.first_N nbinders formals  in
              match uu____9177 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____9274  ->
                         fun uu____9275  ->
                           match (uu____9274, uu____9275) with
                           | ((formal,uu____9301),(binder,uu____9303)) ->
                               let uu____9324 =
                                 let uu____9331 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9331)  in
                               FStar_Syntax_Syntax.NT uu____9324) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9345 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9386  ->
                              match uu____9386 with
                              | (x,i) ->
                                  let uu____9405 =
                                    let uu___521_9406 = x  in
                                    let uu____9407 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___521_9406.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___521_9406.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9407
                                    }  in
                                  (uu____9405, i)))
                       in
                    FStar_All.pipe_right uu____9345
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9431 =
                      let uu____9436 = FStar_Syntax_Subst.compress body  in
                      let uu____9437 =
                        let uu____9438 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9438
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9436 uu____9437
                       in
                    uu____9431 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___528_9487 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___528_9487.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___528_9487.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___528_9487.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___528_9487.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___528_9487.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___528_9487.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___528_9487.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___528_9487.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___528_9487.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___528_9487.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___528_9487.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___528_9487.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___528_9487.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___528_9487.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___528_9487.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___528_9487.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___528_9487.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___528_9487.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___528_9487.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___528_9487.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___528_9487.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___528_9487.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___528_9487.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___528_9487.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___528_9487.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___528_9487.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___528_9487.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___528_9487.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___528_9487.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___528_9487.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___528_9487.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___528_9487.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___528_9487.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___528_9487.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___528_9487.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___528_9487.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___528_9487.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___528_9487.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___528_9487.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___528_9487.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___528_9487.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___528_9487.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___528_9487.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___528_9487.FStar_TypeChecker_Env.erasable_types_tab)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____9559  ->
                       fun uu____9560  ->
                         match (uu____9559, uu____9560) with
                         | ((x,uu____9586),(b,uu____9588)) ->
                             let uu____9609 =
                               let uu____9616 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9616)  in
                             FStar_Syntax_Syntax.NT uu____9609) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____9641 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9641
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9670 ->
                    let uu____9677 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____9677
                | uu____9678 when Prims.op_Negation norm1 ->
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
                | uu____9681 ->
                    let uu____9682 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9682)
                 in
              let aux t1 e1 =
                let uu____9724 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9724 with
                | (binders,body,lopt) ->
                    let uu____9756 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9772 -> arrow_formals_comp_norm false t1  in
                    (match uu____9756 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9806 =
                           if nformals < nbinders
                           then
                             let uu____9840 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9840 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9920 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____9920)
                           else
                             if nformals > nbinders
                             then
                               (let uu____9950 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____9950 with
                                | (binders1,body1) ->
                                    let uu____10003 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____10003))
                             else
                               (let uu____10016 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____10016))
                            in
                         (match uu____9806 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10076 = aux t e  in
              match uu____10076 with
              | (binders,body,comp) ->
                  let uu____10122 =
                    let uu____10133 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp
                       in
                    if uu____10133
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body  in
                      let uu____10148 = aux comp1 body1  in
                      match uu____10148 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10122 with
                   | (binders1,body1,comp1) ->
                       let uu____10231 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10231, comp1))
               in
            (try
               (fun uu___598_10258  ->
                  match () with
                  | () ->
                      let uu____10265 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10265
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10281 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10344  ->
                                   fun lb  ->
                                     match uu____10344 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10399 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10399
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10405 =
                                             let uu____10414 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10414
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10405 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10281 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10555;
                                    FStar_Syntax_Syntax.lbeff = uu____10556;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10558;
                                    FStar_Syntax_Syntax.lbpos = uu____10559;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10583 =
                                     let uu____10590 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10590 with
                                     | (tcenv',uu____10606,e_t) ->
                                         let uu____10612 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10623 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10612 with
                                          | (e1,t_norm1) ->
                                              ((let uu___661_10640 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___661_10640.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10583 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10650 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10650 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10670 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10670
                                               then
                                                 let uu____10675 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10678 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10675 uu____10678
                                               else ());
                                              (let uu____10683 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10683 with
                                               | (vars,_guards,env'1,binder_decls,uu____10710)
                                                   ->
                                                   let uu____10723 =
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
                                                         let uu____10740 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10740
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10762 =
                                                          let uu____10763 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10764 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10763 fvb
                                                            uu____10764
                                                           in
                                                        (vars, uu____10762))
                                                      in
                                                   (match uu____10723 with
                                                    | (vars1,app) ->
                                                        let uu____10775 =
                                                          let is_logical =
                                                            let uu____10788 =
                                                              let uu____10789
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10789.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10788
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10795 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10799 =
                                                              let uu____10800
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10800
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10799
                                                              (fun lid  ->
                                                                 let uu____10809
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10809
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10810 =
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
                                                          if uu____10810
                                                          then
                                                            let uu____10826 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10827 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10826,
                                                              uu____10827)
                                                          else
                                                            (let uu____10838
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10838))
                                                           in
                                                        (match uu____10775
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10862
                                                                 =
                                                                 let uu____10870
                                                                   =
                                                                   let uu____10871
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10872
                                                                    =
                                                                    let uu____10883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10883)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10871
                                                                    uu____10872
                                                                    in
                                                                 let uu____10892
                                                                   =
                                                                   let uu____10893
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10893
                                                                    in
                                                                 (uu____10870,
                                                                   uu____10892,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10862
                                                                in
                                                             let uu____10899
                                                               =
                                                               let uu____10902
                                                                 =
                                                                 let uu____10905
                                                                   =
                                                                   let uu____10908
                                                                    =
                                                                    let uu____10911
                                                                    =
                                                                    let uu____10914
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10914
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10911
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10908
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10905
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10902
                                                                in
                                                             (uu____10899,
                                                               env2)))))))
                               | uu____10923 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10983 =
                                   let uu____10989 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____10989,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____10983  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10995 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11048  ->
                                         fun fvb  ->
                                           match uu____11048 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11103 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11103
                                                  in
                                               let gtok =
                                                 let uu____11107 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11107
                                                  in
                                               let env4 =
                                                 let uu____11110 =
                                                   let uu____11113 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _11119  ->
                                                        FStar_Pervasives_Native.Some
                                                          _11119) uu____11113
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11110
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10995 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11239
                                     t_norm uu____11241 =
                                     match (uu____11239, uu____11241) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11271;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11272;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11274;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11275;_})
                                         ->
                                         let uu____11302 =
                                           let uu____11309 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11309 with
                                           | (tcenv',uu____11325,e_t) ->
                                               let uu____11331 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11342 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11331 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___748_11359 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___748_11359.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11302 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11372 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11372
                                                then
                                                  let uu____11377 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11379 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11381 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11377 uu____11379
                                                    uu____11381
                                                else ());
                                               (let uu____11386 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11386 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11413 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____11413 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11435 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11435
                                                           then
                                                             let uu____11440
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11442
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11445
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11447
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11440
                                                               uu____11442
                                                               uu____11445
                                                               uu____11447
                                                           else ());
                                                          (let uu____11452 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11452
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11481)
                                                               ->
                                                               let uu____11494
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11507
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11507,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11511
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11511
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11524
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11524,
                                                                    decls0))
                                                                  in
                                                               (match uu____11494
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
                                                                    let uu____11545
                                                                    =
                                                                    let uu____11557
                                                                    =
                                                                    let uu____11560
                                                                    =
                                                                    let uu____11563
                                                                    =
                                                                    let uu____11566
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11566
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11563
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11560
                                                                     in
                                                                    (g,
                                                                    uu____11557,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11545
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
                                                                    let uu____11596
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11596
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
                                                                    let uu____11611
                                                                    =
                                                                    let uu____11614
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11614
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11611
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11620
                                                                    =
                                                                    let uu____11623
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11623
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11620
                                                                     in
                                                                    let uu____11628
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11628
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11644
                                                                    =
                                                                    let uu____11652
                                                                    =
                                                                    let uu____11653
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11654
                                                                    =
                                                                    let uu____11670
                                                                    =
                                                                    let uu____11671
                                                                    =
                                                                    let uu____11676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11676)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11671
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11670)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11653
                                                                    uu____11654
                                                                     in
                                                                    let uu____11690
                                                                    =
                                                                    let uu____11691
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11691
                                                                     in
                                                                    (uu____11652,
                                                                    uu____11690,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11644
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11698
                                                                    =
                                                                    let uu____11706
                                                                    =
                                                                    let uu____11707
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11708
                                                                    =
                                                                    let uu____11719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11719)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11707
                                                                    uu____11708
                                                                     in
                                                                    (uu____11706,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11698
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11733
                                                                    =
                                                                    let uu____11741
                                                                    =
                                                                    let uu____11742
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11743
                                                                    =
                                                                    let uu____11754
                                                                    =
                                                                    let uu____11755
                                                                    =
                                                                    let uu____11760
                                                                    =
                                                                    let uu____11761
                                                                    =
                                                                    let uu____11764
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero
                                                                     in
                                                                    uu____11764
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11761
                                                                     in
                                                                    (gsapp,
                                                                    uu____11760)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11755
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11754)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11742
                                                                    uu____11743
                                                                     in
                                                                    (uu____11741,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11733
                                                                     in
                                                                    let uu____11778
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
                                                                    let uu____11790
                                                                    =
                                                                    let uu____11791
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11791
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11790
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head1
                                                                    =
                                                                    let uu____11795
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11795
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11804
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11805
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head1
                                                                    vars1
                                                                    guards1
                                                                    uu____11805
                                                                     in
                                                                    let uu____11807
                                                                    =
                                                                    let uu____11815
                                                                    =
                                                                    let uu____11816
                                                                    =
                                                                    let uu____11821
                                                                    =
                                                                    let uu____11822
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11823
                                                                    =
                                                                    let uu____11834
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11834)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11822
                                                                    uu____11823
                                                                     in
                                                                    (uu____11821,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11816
                                                                     in
                                                                    (uu____11815,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11807
                                                                     in
                                                                    let uu____11847
                                                                    =
                                                                    let uu____11856
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11856
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11871
                                                                    =
                                                                    let uu____11874
                                                                    =
                                                                    let uu____11875
                                                                    =
                                                                    let uu____11883
                                                                    =
                                                                    let uu____11884
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11885
                                                                    =
                                                                    let uu____11896
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11896)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11884
                                                                    uu____11885
                                                                     in
                                                                    (uu____11883,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11875
                                                                     in
                                                                    [uu____11874]
                                                                     in
                                                                    (d3,
                                                                    uu____11871)
                                                                     in
                                                                    match uu____11847
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11778
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____11953
                                                                    =
                                                                    let uu____11956
                                                                    =
                                                                    let uu____11959
                                                                    =
                                                                    let uu____11962
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____11962
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____11959
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____11956
                                                                     in
                                                                    let uu____11969
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____11953,
                                                                    uu____11969,
                                                                    env02))))))))))
                                      in
                                   let uu____11974 =
                                     let uu____11987 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12050  ->
                                          fun uu____12051  ->
                                            match (uu____12050, uu____12051)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12176 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12176 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11987
                                      in
                                   (match uu____11974 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12243 =
                                          let isDeclFun uu___1_12260 =
                                            match uu___1_12260 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12262 -> true
                                            | uu____12275 -> false  in
                                          let uu____12277 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12277
                                            (fun decls3  ->
                                               let uu____12307 =
                                                 FStar_List.fold_left
                                                   (fun uu____12338  ->
                                                      fun elt  ->
                                                        match uu____12338
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12379 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12379
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12407
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12407
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
                                                                    let uu___846_12445
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___846_12445.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___846_12445.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___846_12445.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12307 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12477 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12477, elts, rest))
                                           in
                                        (match uu____12243 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12506 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12512  ->
                                        match uu___2_12512 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12515 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12523 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12523)))
                                in
                             if uu____12506
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___863_12545  ->
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
                                      let uu____12590 = FStar_List.hd names1
                                         in
                                      FStar_All.pipe_right uu____12590
                                        FStar_Pervasives_Native.snd
                                       in
                                    ((let uu____12608 =
                                        let uu____12618 =
                                          let uu____12626 =
                                            let uu____12628 =
                                              let uu____12630 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names1
                                                 in
                                              FStar_All.pipe_right
                                                uu____12630
                                                (FStar_String.concat ",")
                                               in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12628
                                              (if plural
                                               then "their"
                                               else "its")
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12626, r)
                                           in
                                        [uu____12618]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12608);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12689 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12689
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12708 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12708, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12764 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12764 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____12770 = encode_sigelt' env se  in
      match uu____12770 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12782 =
                  let uu____12785 =
                    let uu____12786 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12786  in
                  [uu____12785]  in
                FStar_All.pipe_right uu____12782
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12791 ->
                let uu____12792 =
                  let uu____12795 =
                    let uu____12798 =
                      let uu____12799 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12799  in
                    [uu____12798]  in
                  FStar_All.pipe_right uu____12795
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12806 =
                  let uu____12809 =
                    let uu____12812 =
                      let uu____12815 =
                        let uu____12816 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12816  in
                      [uu____12815]  in
                    FStar_All.pipe_right uu____12812
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12809  in
                FStar_List.append uu____12792 uu____12806
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12830 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12830
       then
         let uu____12835 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12835
       else ());
      (let is_opaque_to_smt t =
         let uu____12847 =
           let uu____12848 = FStar_Syntax_Subst.compress t  in
           uu____12848.FStar_Syntax_Syntax.n  in
         match uu____12847 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12853)) -> s = "opaque_to_smt"
         | uu____12858 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12867 =
           let uu____12868 = FStar_Syntax_Subst.compress t  in
           uu____12868.FStar_Syntax_Syntax.n  in
         match uu____12867 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12873)) -> s = "uninterpreted_by_smt"
         | uu____12878 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____12884 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12896 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____12897 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12898 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____12911 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____12913 =
             let uu____12915 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____12915  in
           if uu____12913
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____12944 ->
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
                  let uu____12977 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____12977  in
                let uu____12978 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____12978 with
                | (formals,uu____12998) ->
                    let arity = FStar_List.length formals  in
                    let uu____13022 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____13022 with
                     | (aname,atok,env2) ->
                         let uu____13044 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____13044 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____13060 =
                                  let uu____13061 =
                                    let uu____13073 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13093  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____13073,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____13061
                                   in
                                [uu____13060;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13110 =
                                let aux uu____13156 uu____13157 =
                                  match (uu____13156, uu____13157) with
                                  | ((bv,uu____13201),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13233 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13233 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13256 =
                                             let uu____13259 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13259 :: acc_sorts  in
                                           (env4, uu____13256, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13110 with
                               | (uu____13291,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13307 =
                                       let uu____13315 =
                                         let uu____13316 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13317 =
                                           let uu____13328 =
                                             let uu____13329 =
                                               let uu____13334 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13334)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13329
                                              in
                                           ([[app]], xs_sorts, uu____13328)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13316 uu____13317
                                          in
                                       (uu____13315,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13307
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13349 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13349
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13352 =
                                       let uu____13360 =
                                         let uu____13361 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13362 =
                                           let uu____13373 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13373)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13361 uu____13362
                                          in
                                       (uu____13360,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13352
                                      in
                                   let uu____13386 =
                                     let uu____13389 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13389  in
                                   (env2, uu____13386))))
                 in
              let uu____13398 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13398 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13424,uu____13425)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13426 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4))
              in
           (match uu____13426 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13448,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13455 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13461  ->
                       match uu___3_13461 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13464 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13470 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13473 -> false))
                in
             Prims.op_Negation uu____13455  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13483 =
                let uu____13488 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13488 env fv t quals  in
              match uu____13483 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____13502 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13502  in
                  let uu____13505 =
                    let uu____13506 =
                      let uu____13509 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13509
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13506  in
                  (uu____13505, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13519 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13519 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1004_13531 = env  in
                  let uu____13532 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1004_13531.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1004_13531.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1004_13531.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13532;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1004_13531.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1004_13531.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1004_13531.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1004_13531.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1004_13531.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1004_13531.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1004_13531.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13534 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13534 with
                 | (f3,decls) ->
                     let g =
                       let uu____13548 =
                         let uu____13551 =
                           let uu____13552 =
                             let uu____13560 =
                               let uu____13561 =
                                 let uu____13563 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13563
                                  in
                               FStar_Pervasives_Native.Some uu____13561  in
                             let uu____13567 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.op_Hat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____13560, uu____13567)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13552  in
                         [uu____13551]  in
                       FStar_All.pipe_right uu____13548
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13576) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13590 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13612 =
                        let uu____13615 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13615.FStar_Syntax_Syntax.fv_name  in
                      uu____13612.FStar_Syntax_Syntax.v  in
                    let uu____13616 =
                      let uu____13618 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13618  in
                    if uu____13616
                    then
                      let val_decl =
                        let uu___1021_13650 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1021_13650.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1021_13650.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1021_13650.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1021_13650.FStar_Syntax_Syntax.sigopts)
                        }  in
                      let uu____13651 = encode_sigelt' env1 val_decl  in
                      match uu____13651 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13590 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13687,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____13689;
                           FStar_Syntax_Syntax.lbtyp = uu____13690;
                           FStar_Syntax_Syntax.lbeff = uu____13691;
                           FStar_Syntax_Syntax.lbdef = uu____13692;
                           FStar_Syntax_Syntax.lbattrs = uu____13693;
                           FStar_Syntax_Syntax.lbpos = uu____13694;_}::[]),uu____13695)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____13714 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one
              in
           (match uu____13714 with
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
                  let uu____13752 =
                    let uu____13755 =
                      let uu____13756 =
                        let uu____13764 =
                          let uu____13765 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____13766 =
                            let uu____13777 =
                              let uu____13778 =
                                let uu____13783 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13783)  in
                              FStar_SMTEncoding_Util.mkEq uu____13778  in
                            ([[b2t_x]], [xx], uu____13777)  in
                          FStar_SMTEncoding_Term.mkForall uu____13765
                            uu____13766
                           in
                        (uu____13764,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13756  in
                    [uu____13755]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13752
                   in
                let uu____13821 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13821, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13824,uu____13825) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13835  ->
                   match uu___4_13835 with
                   | FStar_Syntax_Syntax.Discriminator uu____13837 -> true
                   | uu____13839 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13841,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13853 =
                      let uu____13855 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____13855.FStar_Ident.idText  in
                    uu____13853 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13862  ->
                      match uu___5_13862 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13865 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13868) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13882  ->
                   match uu___6_13882 with
                   | FStar_Syntax_Syntax.Projector uu____13884 -> true
                   | uu____13890 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13894 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13894 with
            | FStar_Pervasives_Native.Some uu____13901 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1086_13903 = se  in
                  let uu____13904 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13904;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1086_13903.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1086_13903.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1086_13903.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1086_13903.FStar_Syntax_Syntax.sigopts)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13907) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1098_13928 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1098_13928.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1098_13928.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1098_13928.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1098_13928.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1098_13928.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13933) ->
           let uu____13942 = encode_sigelts env ses  in
           (match uu____13942 with
            | (g,env1) ->
                let uu____13953 =
                  FStar_List.fold_left
                    (fun uu____13977  ->
                       fun elt  ->
                         match uu____13977 with
                         | (g',inversions) ->
                             let uu____14005 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_14028  ->
                                       match uu___7_14028 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____14030;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____14031;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____14032;_}
                                           -> false
                                       | uu____14039 -> true))
                                in
                             (match uu____14005 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1124_14064 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1124_14064.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1124_14064.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1124_14064.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____13953 with
                 | (g',inversions) ->
                     let uu____14083 =
                       FStar_List.fold_left
                         (fun uu____14114  ->
                            fun elt  ->
                              match uu____14114 with
                              | (decls,elts,rest) ->
                                  let uu____14155 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14164  ->
                                            match uu___8_14164 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14166 -> true
                                            | uu____14179 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14155
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14202 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14223  ->
                                               match uu___9_14223 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14225 -> true
                                               | uu____14238 -> false))
                                        in
                                     match uu____14202 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1146_14269 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1146_14269.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1146_14269.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1146_14269.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____14083 with
                      | (decls,elts,rest) ->
                          let uu____14295 =
                            let uu____14296 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14303 =
                              let uu____14306 =
                                let uu____14309 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14309  in
                              FStar_List.append elts uu____14306  in
                            FStar_List.append uu____14296 uu____14303  in
                          (uu____14295, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14320,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14333 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14333 with
             | (usubst,uvs) ->
                 let uu____14353 =
                   let uu____14360 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14361 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14362 =
                     let uu____14363 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14363 k  in
                   (uu____14360, uu____14361, uu____14362)  in
                 (match uu____14353 with
                  | (env1,tps1,k1) ->
                      let uu____14376 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14376 with
                       | (tps2,k2) ->
                           let uu____14384 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14384 with
                            | (uu____14400,k3) ->
                                let uu____14422 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2
                                   in
                                (match uu____14422 with
                                 | (tps3,env_tps,uu____14434,us) ->
                                     let u_k =
                                       let uu____14437 =
                                         let uu____14438 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14439 =
                                           let uu____14444 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  Prims.int_zero)
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14446 =
                                             let uu____14447 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14447
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14444 uu____14446
                                            in
                                         uu____14439
                                           FStar_Pervasives_Native.None
                                           uu____14438
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14437 k3
                                        in
                                     let rec universe_leq u v1 =
                                       match (u, v1) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14465) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14471,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14474) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  ->
                                                   universe_leq u1 v1))
                                       | (uu____14482,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14489) ->
                                           let uu____14490 =
                                             let uu____14492 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14492
                                              in
                                           failwith uu____14490
                                       | (uu____14496,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14497 =
                                             let uu____14499 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14499
                                              in
                                           failwith uu____14497
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14503,uu____14504) ->
                                           let uu____14513 =
                                             let uu____14515 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14515
                                              in
                                           failwith uu____14513
                                       | (uu____14519,FStar_Syntax_Syntax.U_unif
                                          uu____14520) ->
                                           let uu____14529 =
                                             let uu____14531 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14531
                                              in
                                           failwith uu____14529
                                       | uu____14535 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14548 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14548 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14566 = u_leq_u_k u_tp  in
                                       if uu____14566
                                       then true
                                       else
                                         (let uu____14573 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14573 with
                                          | (formals,uu____14590) ->
                                              let uu____14611 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals
                                                 in
                                              (match uu____14611 with
                                               | (uu____14621,uu____14622,uu____14623,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14634 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14634
             then
               let uu____14639 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14639
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14659  ->
                       match uu___10_14659 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14663 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14676 = c  in
                 match uu____14676 with
                 | (name,args,uu____14681,uu____14682,uu____14683) ->
                     let uu____14694 =
                       let uu____14695 =
                         let uu____14707 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14734  ->
                                   match uu____14734 with
                                   | (uu____14743,sort,uu____14745) -> sort))
                            in
                         (name, uu____14707,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14695  in
                     [uu____14694]
               else
                 (let uu____14756 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14756 c)
                in
             let inversion_axioms tapp vars =
               let uu____14774 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l  ->
                         let uu____14782 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l
                            in
                         FStar_All.pipe_right uu____14782 FStar_Option.isNone))
                  in
               if uu____14774
               then []
               else
                 (let uu____14817 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort
                     in
                  match uu____14817 with
                  | (xxsym,xx) ->
                      let uu____14830 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____14869  ->
                                fun l  ->
                                  match uu____14869 with
                                  | (out,decls) ->
                                      let uu____14889 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l
                                         in
                                      (match uu____14889 with
                                       | (uu____14900,data_t) ->
                                           let uu____14902 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t
                                              in
                                           (match uu____14902 with
                                            | (args,res) ->
                                                let indices =
                                                  let uu____14946 =
                                                    let uu____14947 =
                                                      FStar_Syntax_Subst.compress
                                                        res
                                                       in
                                                    uu____14947.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____14946 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____14950,indices)
                                                      -> indices
                                                  | uu____14976 -> []  in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1  ->
                                                          fun uu____15006  ->
                                                            match uu____15006
                                                            with
                                                            | (x,uu____15014)
                                                                ->
                                                                let uu____15019
                                                                  =
                                                                  let uu____15020
                                                                    =
                                                                    let uu____15028
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                    (uu____15028,
                                                                    [xx])  in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____15020
                                                                   in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____15019)
                                                       env)
                                                   in
                                                let uu____15033 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1
                                                   in
                                                (match uu____15033 with
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
                                                                  let uu____15068
                                                                    =
                                                                    let uu____15073
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    (uu____15073,
                                                                    a)  in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____15068)
                                                             vars indices1
                                                         else []  in
                                                       let uu____15076 =
                                                         let uu____15077 =
                                                           let uu____15082 =
                                                             let uu____15083
                                                               =
                                                               let uu____15088
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx
                                                                  in
                                                               let uu____15089
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l
                                                                  in
                                                               (uu____15088,
                                                                 uu____15089)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____15083
                                                              in
                                                           (out, uu____15082)
                                                            in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____15077
                                                          in
                                                       (uu____15076,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, []))
                         in
                      (match uu____14830 with
                       | (data_ax,decls) ->
                           let uu____15104 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort
                              in
                           (match uu____15104 with
                            | (ffsym,ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu____15121 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff])
                                         in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____15121 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp
                                     in
                                  let uu____15128 =
                                    let uu____15136 =
                                      let uu____15137 =
                                        FStar_Ident.range_of_lid t  in
                                      let uu____15138 =
                                        let uu____15149 =
                                          let uu____15150 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort)
                                             in
                                          let uu____15152 =
                                            let uu____15155 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               in
                                            uu____15155 :: vars  in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____15150 uu____15152
                                           in
                                        let uu____15157 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax)
                                           in
                                        ([[xx_has_type_sfuel]], uu____15149,
                                          uu____15157)
                                         in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____15137 uu____15138
                                       in
                                    let uu____15166 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        (Prims.op_Hat
                                           "fuel_guarded_inversion_"
                                           t.FStar_Ident.str)
                                       in
                                    (uu____15136,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____15166)
                                     in
                                  FStar_SMTEncoding_Util.mkAssume uu____15128
                                   in
                                let uu____15172 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls uu____15172)))
                in
             let uu____15179 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15201 ->
                     let uu____15202 =
                       let uu____15209 =
                         let uu____15210 =
                           let uu____15225 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15225)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15210  in
                       FStar_Syntax_Syntax.mk uu____15209  in
                     uu____15202 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15179 with
             | (formals,res) ->
                 let uu____15265 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15265 with
                  | (vars,guards,env',binder_decls,uu____15290) ->
                      let arity = FStar_List.length vars  in
                      let uu____15304 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15304 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15330 =
                               let uu____15338 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15338)  in
                             FStar_SMTEncoding_Util.mkApp uu____15330  in
                           let uu____15344 =
                             let tname_decl =
                               let uu____15354 =
                                 let uu____15355 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15374 =
                                             let uu____15376 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15376
                                              in
                                           let uu____15378 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15374, uu____15378, false)))
                                    in
                                 let uu____15382 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15355,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15382, false)
                                  in
                               constructor_or_logic_type_decl uu____15354  in
                             let uu____15390 =
                               match vars with
                               | [] ->
                                   let uu____15403 =
                                     let uu____15404 =
                                       let uu____15407 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun _15413  ->
                                            FStar_Pervasives_Native.Some
                                              _15413) uu____15407
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15404
                                      in
                                   ([], uu____15403)
                               | uu____15416 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15426 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15426
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15442 =
                                       let uu____15450 =
                                         let uu____15451 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15452 =
                                           let uu____15468 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15468)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15451 uu____15452
                                          in
                                       (uu____15450,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15442
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15390 with
                             | (tok_decls,env2) ->
                                 let uu____15495 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15495
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15344 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15523 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15523 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____15545 =
                                            let uu____15546 =
                                              let uu____15554 =
                                                let uu____15555 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15555
                                                 in
                                              (uu____15554,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15546
                                             in
                                          [uu____15545]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15565 =
                                          FStar_List.map
                                            (fun uu____15569  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15565 true
                                         in
                                      let uu____15571 =
                                        let uu____15574 =
                                          let uu____15577 =
                                            let uu____15580 =
                                              let uu____15581 =
                                                let uu____15589 =
                                                  let uu____15590 =
                                                    let uu____15595 =
                                                      let uu____15596 =
                                                        let uu____15607 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15607)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15596
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15595)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15590
                                                   in
                                                (uu____15589,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15581
                                               in
                                            [uu____15580]  in
                                          FStar_List.append karr uu____15577
                                           in
                                        FStar_All.pipe_right uu____15574
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15571
                                   in
                                let aux =
                                  let uu____15626 =
                                    let uu____15629 =
                                      inversion_axioms tapp vars  in
                                    let uu____15632 =
                                      let uu____15635 =
                                        let uu____15638 =
                                          let uu____15639 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15639 env2 tapp
                                            vars
                                           in
                                        [uu____15638]  in
                                      FStar_All.pipe_right uu____15635
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15629 uu____15632
                                     in
                                  FStar_List.append kindingAx uu____15626  in
                                let g =
                                  let uu____15647 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15647
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15655,uu____15656,uu____15657,uu____15658,uu____15659)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15667,t,uu____15669,n_tps,uu____15671) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15682 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15682 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15730 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15730 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15754 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15754 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15774 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15774 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15853 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15853,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15860 =
                                   let uu____15861 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15861, true)
                                    in
                                 let uu____15869 =
                                   let uu____15876 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15876
                                    in
                                 FStar_All.pipe_right uu____15860 uu____15869
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
                               let uu____15888 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15888 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15900::uu____15901 ->
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
                                            let uu____15950 =
                                              let uu____15951 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15951]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15950
                                             in
                                          let uu____15977 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15978 =
                                            let uu____15989 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15989)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15977 uu____15978
                                      | uu____16016 -> tok_typing  in
                                    let uu____16027 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____16027 with
                                     | (vars',guards',env'',decls_formals,uu____16052)
                                         ->
                                         let uu____16065 =
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
                                         (match uu____16065 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____16095 ->
                                                    let uu____16104 =
                                                      let uu____16105 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16105
                                                       in
                                                    [uu____16104]
                                                 in
                                              let encode_elim uu____16121 =
                                                let uu____16122 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16122 with
                                                | (head1,args) ->
                                                    let uu____16173 =
                                                      let uu____16174 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____16174.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16173 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16186;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16187;_},uu____16188)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16194 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16194
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
                                                                  | uu____16257
                                                                    ->
                                                                    let uu____16258
                                                                    =
                                                                    let uu____16264
                                                                    =
                                                                    let uu____16266
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16266
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16264)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16258
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16289
                                                                    =
                                                                    let uu____16291
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16291
                                                                     in
                                                                    if
                                                                    uu____16289
                                                                    then
                                                                    let uu____16313
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16313]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16316
                                                                =
                                                                let uu____16330
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16387
                                                                     ->
                                                                    fun
                                                                    uu____16388
                                                                     ->
                                                                    match 
                                                                    (uu____16387,
                                                                    uu____16388)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16499
                                                                    =
                                                                    let uu____16507
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16507
                                                                     in
                                                                    (match uu____16499
                                                                    with
                                                                    | 
                                                                    (uu____16521,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16532
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16532
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16537
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16537
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
                                                                  uu____16330
                                                                 in
                                                              (match uu____16316
                                                               with
                                                               | (uu____16558,arg_vars,elim_eqns_or_guards,uu____16561)
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
                                                                    let uu____16588
                                                                    =
                                                                    let uu____16596
                                                                    =
                                                                    let uu____16597
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16598
                                                                    =
                                                                    let uu____16609
                                                                    =
                                                                    let uu____16610
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16610
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16612
                                                                    =
                                                                    let uu____16613
                                                                    =
                                                                    let uu____16618
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16618)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16613
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16609,
                                                                    uu____16612)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16597
                                                                    uu____16598
                                                                     in
                                                                    (uu____16596,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16588
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____16633
                                                                    =
                                                                    let uu____16634
                                                                    =
                                                                    let uu____16640
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16640,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16634
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16633
                                                                     in
                                                                    let uu____16643
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____16643
                                                                    then
                                                                    let x =
                                                                    let uu____16647
                                                                    =
                                                                    let uu____16653
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____16653,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16647
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____16658
                                                                    =
                                                                    let uu____16666
                                                                    =
                                                                    let uu____16667
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16668
                                                                    =
                                                                    let uu____16679
                                                                    =
                                                                    let uu____16684
                                                                    =
                                                                    let uu____16687
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____16687]
                                                                     in
                                                                    [uu____16684]
                                                                     in
                                                                    let uu____16692
                                                                    =
                                                                    let uu____16693
                                                                    =
                                                                    let uu____16698
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____16700
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____16698,
                                                                    uu____16700)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16693
                                                                     in
                                                                    (uu____16679,
                                                                    [x],
                                                                    uu____16692)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16667
                                                                    uu____16668
                                                                     in
                                                                    let uu____16721
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____16666,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16721)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16658
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16732
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
                                                                    (let uu____16755
                                                                    =
                                                                    let uu____16756
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____16756
                                                                    dapp1  in
                                                                    [uu____16755])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16732
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16763
                                                                    =
                                                                    let uu____16771
                                                                    =
                                                                    let uu____16772
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16773
                                                                    =
                                                                    let uu____16784
                                                                    =
                                                                    let uu____16785
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16785
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16787
                                                                    =
                                                                    let uu____16788
                                                                    =
                                                                    let uu____16793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16793)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16788
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16784,
                                                                    uu____16787)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16772
                                                                    uu____16773
                                                                     in
                                                                    (uu____16771,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16763)
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
                                                         let uu____16812 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16812
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
                                                                  | uu____16875
                                                                    ->
                                                                    let uu____16876
                                                                    =
                                                                    let uu____16882
                                                                    =
                                                                    let uu____16884
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16884
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16882)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16876
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16907
                                                                    =
                                                                    let uu____16909
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16909
                                                                     in
                                                                    if
                                                                    uu____16907
                                                                    then
                                                                    let uu____16931
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16931]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16934
                                                                =
                                                                let uu____16948
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____17005
                                                                     ->
                                                                    fun
                                                                    uu____17006
                                                                     ->
                                                                    match 
                                                                    (uu____17005,
                                                                    uu____17006)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____17117
                                                                    =
                                                                    let uu____17125
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____17125
                                                                     in
                                                                    (match uu____17117
                                                                    with
                                                                    | 
                                                                    (uu____17139,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17150
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____17150
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17155
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____17155
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
                                                                  uu____16948
                                                                 in
                                                              (match uu____16934
                                                               with
                                                               | (uu____17176,arg_vars,elim_eqns_or_guards,uu____17179)
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
                                                                    let uu____17206
                                                                    =
                                                                    let uu____17214
                                                                    =
                                                                    let uu____17215
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17216
                                                                    =
                                                                    let uu____17227
                                                                    =
                                                                    let uu____17228
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17228
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17230
                                                                    =
                                                                    let uu____17231
                                                                    =
                                                                    let uu____17236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17236)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17231
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17227,
                                                                    uu____17230)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17215
                                                                    uu____17216
                                                                     in
                                                                    (uu____17214,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17206
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____17251
                                                                    =
                                                                    let uu____17252
                                                                    =
                                                                    let uu____17258
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17258,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17252
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17251
                                                                     in
                                                                    let uu____17261
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____17261
                                                                    then
                                                                    let x =
                                                                    let uu____17265
                                                                    =
                                                                    let uu____17271
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____17271,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17265
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____17276
                                                                    =
                                                                    let uu____17284
                                                                    =
                                                                    let uu____17285
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17286
                                                                    =
                                                                    let uu____17297
                                                                    =
                                                                    let uu____17302
                                                                    =
                                                                    let uu____17305
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____17305]
                                                                     in
                                                                    [uu____17302]
                                                                     in
                                                                    let uu____17310
                                                                    =
                                                                    let uu____17311
                                                                    =
                                                                    let uu____17316
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____17318
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____17316,
                                                                    uu____17318)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17311
                                                                     in
                                                                    (uu____17297,
                                                                    [x],
                                                                    uu____17310)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17285
                                                                    uu____17286
                                                                     in
                                                                    let uu____17339
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____17284,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____17339)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17276
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____17350
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
                                                                    (let uu____17373
                                                                    =
                                                                    let uu____17374
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____17374
                                                                    dapp1  in
                                                                    [uu____17373])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17350
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17381
                                                                    =
                                                                    let uu____17389
                                                                    =
                                                                    let uu____17390
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17391
                                                                    =
                                                                    let uu____17402
                                                                    =
                                                                    let uu____17403
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17403
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17405
                                                                    =
                                                                    let uu____17406
                                                                    =
                                                                    let uu____17411
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17411)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17406
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17402,
                                                                    uu____17405)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17390
                                                                    uu____17391
                                                                     in
                                                                    (uu____17389,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17381)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17428 ->
                                                         ((let uu____17430 =
                                                             let uu____17436
                                                               =
                                                               let uu____17438
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17440
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17438
                                                                 uu____17440
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17436)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17430);
                                                          ([], [])))
                                                 in
                                              let uu____17448 =
                                                encode_elim ()  in
                                              (match uu____17448 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17474 =
                                                       let uu____17477 =
                                                         let uu____17480 =
                                                           let uu____17483 =
                                                             let uu____17486
                                                               =
                                                               let uu____17489
                                                                 =
                                                                 let uu____17492
                                                                   =
                                                                   let uu____17493
                                                                    =
                                                                    let uu____17505
                                                                    =
                                                                    let uu____17506
                                                                    =
                                                                    let uu____17508
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17508
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17506
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17505)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17493
                                                                    in
                                                                 [uu____17492]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17489
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17486
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17519 =
                                                             let uu____17522
                                                               =
                                                               let uu____17525
                                                                 =
                                                                 let uu____17528
                                                                   =
                                                                   let uu____17531
                                                                    =
                                                                    let uu____17534
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
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
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17564)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17552
                                                                    uu____17553
                                                                     in
                                                                    (uu____17551,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17543
                                                                     in
                                                                    let uu____17577
                                                                    =
                                                                    let uu____17580
                                                                    =
                                                                    let uu____17581
                                                                    =
                                                                    let uu____17589
                                                                    =
                                                                    let uu____17590
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17591
                                                                    =
                                                                    let uu____17602
                                                                    =
                                                                    let uu____17603
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17603
                                                                    vars'  in
                                                                    let uu____17605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17602,
                                                                    uu____17605)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17590
                                                                    uu____17591
                                                                     in
                                                                    (uu____17589,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17581
                                                                     in
                                                                    [uu____17580]
                                                                     in
                                                                    uu____17542
                                                                    ::
                                                                    uu____17577
                                                                     in
                                                                    uu____17534
                                                                    ::
                                                                    uu____17539
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17531
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17528
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17525
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17522
                                                              in
                                                           FStar_List.append
                                                             uu____17483
                                                             uu____17519
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17480
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17477
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17474
                                                      in
                                                   let uu____17622 =
                                                     let uu____17623 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17623 g
                                                      in
                                                   (uu____17622, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17657  ->
              fun se  ->
                match uu____17657 with
                | (g,env1) ->
                    let uu____17677 = encode_sigelt env1 se  in
                    (match uu____17677 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17745 =
        match uu____17745 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17782 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17790 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17790
                   then
                     let uu____17795 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17797 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17799 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17795 uu____17797 uu____17799
                   else ());
                  (let uu____17804 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17804 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17822 =
                         let uu____17830 =
                           let uu____17832 =
                             let uu____17834 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17834
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17832  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17830
                          in
                       (match uu____17822 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17854 = FStar_Options.log_queries ()
                                 in
                              if uu____17854
                              then
                                let uu____17857 =
                                  let uu____17859 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17861 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17863 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17859 uu____17861 uu____17863
                                   in
                                FStar_Pervasives_Native.Some uu____17857
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17879 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17889 =
                                let uu____17892 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17892  in
                              FStar_List.append uu____17879 uu____17889  in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17904,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17924 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17924 with
                  | (g,env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env')))
         in
      let uu____17945 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env)
         in
      match uu____17945 with | (uu____17972,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____18025  ->
              match uu____18025 with
              | (l,uu____18034,uu____18035) ->
                  let uu____18038 =
                    let uu____18050 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____18050, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____18038))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____18083  ->
              match uu____18083 with
              | (l,uu____18094,uu____18095) ->
                  let uu____18098 =
                    let uu____18099 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _18102  -> FStar_SMTEncoding_Term.Echo _18102)
                      uu____18099
                     in
                  let uu____18103 =
                    let uu____18106 =
                      let uu____18107 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____18107  in
                    [uu____18106]  in
                  uu____18098 :: uu____18103))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____18125 =
      let uu____18128 =
        let uu____18129 = FStar_Util.psmap_empty ()  in
        let uu____18144 =
          let uu____18153 = FStar_Util.psmap_empty ()  in (uu____18153, [])
           in
        let uu____18160 =
          let uu____18162 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____18162 FStar_Ident.string_of_lid  in
        let uu____18164 = FStar_Util.smap_create (Prims.of_int (100))  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____18129;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18144;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18160;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18164
        }  in
      [uu____18128]  in
    FStar_ST.op_Colon_Equals last_env uu____18125
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____18208 = FStar_ST.op_Bang last_env  in
      match uu____18208 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18236 ->
          let uu___1573_18239 = e  in
          let uu____18240 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1573_18239.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1573_18239.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1573_18239.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1573_18239.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1573_18239.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1573_18239.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1573_18239.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18240;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1573_18239.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1573_18239.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18248 = FStar_ST.op_Bang last_env  in
    match uu____18248 with
    | [] -> failwith "Empty env stack"
    | uu____18275::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____18307  ->
    let uu____18308 = FStar_ST.op_Bang last_env  in
    match uu____18308 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____18368  ->
    let uu____18369 = FStar_ST.op_Bang last_env  in
    match uu____18369 with
    | [] -> failwith "Popping an empty stack"
    | uu____18396::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18433  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18486  ->
         let uu____18487 = snapshot_env ()  in
         match uu____18487 with
         | (env_depth,()) ->
             let uu____18509 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18509 with
              | (varops_depth,()) ->
                  let uu____18531 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18531 with
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
        (fun uu____18589  ->
           let uu____18590 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18590 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18685 = snapshot msg  in () 
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
        | (uu____18731::uu____18732,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1634_18740 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1634_18740.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1634_18740.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1634_18740.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18741 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1640_18768 = elt  in
        let uu____18769 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1640_18768.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1640_18768.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18769;
          FStar_SMTEncoding_Term.a_names =
            (uu___1640_18768.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18789 =
        let uu____18792 =
          let uu____18793 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____18793  in
        let uu____18794 = open_fact_db_tags env  in uu____18792 ::
          uu____18794
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18789
  
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
      let uu____18821 = encode_sigelt env se  in
      match uu____18821 with
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
                (let uu____18867 =
                   let uu____18870 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18870
                    in
                 match uu____18867 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18885 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18885
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18915 = FStar_Options.log_queries ()  in
        if uu____18915
        then
          let uu____18920 =
            let uu____18921 =
              let uu____18923 =
                let uu____18925 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18925 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18923  in
            FStar_SMTEncoding_Term.Caption uu____18921  in
          uu____18920 :: decls
        else decls  in
      (let uu____18944 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18944
       then
         let uu____18947 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18947
       else ());
      (let env =
         let uu____18953 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18953 tcenv  in
       let uu____18954 = encode_top_level_facts env se  in
       match uu____18954 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18968 =
               let uu____18971 =
                 let uu____18974 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18974
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18971  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18968)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____19007 = FStar_Options.log_queries ()  in
          if uu____19007
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1678_19027 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1678_19027.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1678_19027.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1678_19027.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1678_19027.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1678_19027.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1678_19027.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1678_19027.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1678_19027.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1678_19027.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1678_19027.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____19032 =
             let uu____19035 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____19035
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____19032  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____19055 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____19055
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
          (let uu____19079 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____19079
           then
             let uu____19082 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____19082
           else ());
          (let env =
             let uu____19090 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____19090
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____19129  ->
                     fun se  ->
                       match uu____19129 with
                       | (g,env2) ->
                           let uu____19149 = encode_top_level_facts env2 se
                              in
                           (match uu____19149 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____19172 =
             encode_signature
               (let uu___1701_19181 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1701_19181.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1701_19181.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1701_19181.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1701_19181.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1701_19181.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1701_19181.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1701_19181.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1701_19181.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1701_19181.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1701_19181.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____19172 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19197 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19197
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____19203 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____19203))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun tcmod  ->
      fun uu____19231  ->
        match uu____19231 with
        | (decls,fvbs) ->
            let uu____19244 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
            if uu____19244
            then ()
            else
              (let name =
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module")
                   (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               (let uu____19259 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____19259
                then
                  let uu____19262 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int
                     in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19262
                else ());
               (let env =
                  let uu____19270 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv  in
                  FStar_All.pipe_right uu____19270
                    FStar_SMTEncoding_Env.reset_current_module_fvbs
                   in
                let env1 =
                  let uu____19272 = FStar_All.pipe_right fvbs FStar_List.rev
                     in
                  FStar_All.pipe_right uu____19272
                    (FStar_List.fold_left
                       (fun env1  ->
                          fun fvb  ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env)
                   in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19286 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19286
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
        (let uu____19348 =
           let uu____19350 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____19350.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19348);
        (let env =
           let uu____19352 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19352 tcenv  in
         let uu____19353 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19390 = aux rest  in
                 (match uu____19390 with
                  | (out,rest1) ->
                      let t =
                        let uu____19418 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19418 with
                        | FStar_Pervasives_Native.Some uu____19421 ->
                            let uu____19422 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19422
                              x.FStar_Syntax_Syntax.sort
                        | uu____19423 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        norm_with_steps
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19427 =
                        let uu____19430 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1744_19433 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1744_19433.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1744_19433.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19430 :: out  in
                      (uu____19427, rest1))
             | uu____19438 -> ([], bindings)  in
           let uu____19445 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19445 with
           | (closing,bindings) ->
               let uu____19470 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19470, bindings)
            in
         match uu____19353 with
         | (q1,bindings) ->
             let uu____19493 = encode_env_bindings env bindings  in
             (match uu____19493 with
              | (env_decls,env1) ->
                  ((let uu____19515 =
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
                    if uu____19515
                    then
                      let uu____19522 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula {: %s\n"
                        uu____19522
                    else ());
                   (let uu____19527 =
                      FStar_Util.record_time
                        (fun uu____19542  ->
                           FStar_SMTEncoding_EncodeTerm.encode_formula q1
                             env1)
                       in
                    match uu____19527 with
                    | ((phi,qdecls),ms) ->
                        let uu____19566 =
                          let uu____19571 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19571 phi
                           in
                        (match uu____19566 with
                         | (labels,phi1) ->
                             let uu____19588 = encode_labels labels  in
                             (match uu____19588 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19624 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19624
                                    then
                                      let uu____19629 =
                                        let uu____19630 =
                                          let uu____19632 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula : "
                                            uu____19632
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19630
                                         in
                                      [uu____19629]
                                    else []  in
                                  let query_prelude =
                                    let uu____19640 =
                                      let uu____19641 =
                                        let uu____19642 =
                                          let uu____19645 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19652 =
                                            let uu____19655 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19655
                                             in
                                          FStar_List.append uu____19645
                                            uu____19652
                                           in
                                        FStar_List.append env_decls
                                          uu____19642
                                         in
                                      FStar_All.pipe_right uu____19641
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19640
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19665 =
                                      let uu____19673 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19674 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19673,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19674)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19665
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  ((let uu____19687 =
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
                                    if uu____19687
                                    then
                                      FStar_Util.print_string
                                        "} Done encoding\n"
                                    else ());
                                   (let uu____19698 =
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
                                    if uu____19698
                                    then
                                      FStar_Util.print1
                                        "Encoding took %sms\n"
                                        (Prims.string_of_int ms)
                                    else ());
                                   (query_prelude, labels, qry, suffix))))))))
  