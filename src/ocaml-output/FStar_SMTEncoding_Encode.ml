open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] in
      let uu____15 =
        let uu____19 =
          let uu____21 =
            FStar_TypeChecker_Env.current_module
              env.FStar_SMTEncoding_Env.tcenv in
          FStar_Ident.string_of_lid uu____21 in
        FStar_Pervasives_Native.Some uu____19 in
      FStar_Profiling.profile
        (fun uu____24 ->
           FStar_TypeChecker_Normalize.normalize steps
             env.FStar_SMTEncoding_Env.tcenv t) uu____15
        "FStar.TypeChecker.SMTEncoding.Encode.norm_before_encoding"
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu____42 =
          let uu____46 =
            let uu____48 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____48 in
          FStar_Pervasives_Native.Some uu____46 in
        FStar_Profiling.profile
          (fun uu____51 -> FStar_TypeChecker_Normalize.normalize steps env t)
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
  = fun projectee -> match projectee with | { mk; is;_} -> mk
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee -> match projectee with | { mk; is;_} -> is
let (prims : prims_t) =
  let module_name = "Prims" in
  let uu____192 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort in
  match uu____192 with
  | (asym, a) ->
      let uu____203 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort in
      (match uu____203 with
       | (xsym, x) ->
           let uu____214 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort in
           (match uu____214 with
            | (ysym, y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____292 =
                      let uu____304 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort) in
                      (x1, uu____304, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____292 in
                  let xtok = Prims.op_Hat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____324 =
                      let uu____332 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____332) in
                    FStar_SMTEncoding_Util.mkApp uu____324 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars in
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_All.pipe_right (FStar_Util.prefix vars)
                        FStar_Pervasives_Native.fst in
                    let axiom_name = Prims.op_Hat "primitive_tot_fun_" x1 in
                    let tot_fun_axiom_for_x =
                      let uu____427 =
                        let uu____435 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1 in
                        (uu____435, FStar_Pervasives_Native.None, axiom_name) in
                      FStar_SMTEncoding_Util.mkAssume uu____427 in
                    let uu____438 =
                      FStar_List.fold_left
                        (fun uu____492 ->
                           fun var ->
                             match uu____492 with
                             | (axioms, app, vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var] in
                                 let vars2 = FStar_List.append vars1 [var] in
                                 let axiom_name1 =
                                   let uu____619 =
                                     let uu____621 =
                                       let uu____623 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length in
                                       Prims.string_of_int uu____623 in
                                     Prims.op_Hat "." uu____621 in
                                   Prims.op_Hat axiom_name uu____619 in
                                 let uu____645 =
                                   let uu____648 =
                                     let uu____651 =
                                       let uu____652 =
                                         let uu____660 =
                                           let uu____661 =
                                             let uu____672 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1 in
                                             ([[app1]], vars2, uu____672) in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____661 in
                                         (uu____660,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1) in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____652 in
                                     [uu____651] in
                                   FStar_List.append axioms uu____648 in
                                 (uu____645, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one in
                    match uu____438 with
                    | (axioms, uu____718, uu____719) -> axioms in
                  let uu____744 =
                    let uu____747 =
                      let uu____750 =
                        let uu____753 =
                          let uu____756 =
                            let uu____757 =
                              let uu____765 =
                                let uu____766 =
                                  let uu____777 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                  ([[xapp]], vars, uu____777) in
                                FStar_SMTEncoding_Term.mkForall rng uu____766 in
                              (uu____765, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____757 in
                          [uu____756] in
                        xtok_decl :: uu____753 in
                      xname_decl :: uu____750 in
                    let uu____789 =
                      let uu____792 =
                        let uu____795 =
                          let uu____796 =
                            let uu____804 =
                              let uu____805 =
                                let uu____816 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp) in
                                ([[xtok_app]], vars, uu____816) in
                              FStar_SMTEncoding_Term.mkForall rng uu____805 in
                            (uu____804,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____796 in
                        [uu____795] in
                      FStar_List.append tot_fun_axioms uu____792 in
                    FStar_List.append uu____747 uu____789 in
                  (xtok1, (FStar_List.length vars), uu____744) in
                let axy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(asym, FStar_SMTEncoding_Term.Term_sort);
                    (xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims =
                  let uu____986 =
                    let uu____1007 =
                      let uu____1026 =
                        let uu____1027 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____1027 in
                      quant axy uu____1026 in
                    (FStar_Parser_Const.op_Eq, uu____1007) in
                  let uu____1044 =
                    let uu____1067 =
                      let uu____1088 =
                        let uu____1107 =
                          let uu____1108 =
                            let uu____1109 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____1109 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1108 in
                        quant axy uu____1107 in
                      (FStar_Parser_Const.op_notEq, uu____1088) in
                    let uu____1126 =
                      let uu____1149 =
                        let uu____1170 =
                          let uu____1189 =
                            let uu____1190 =
                              let uu____1191 =
                                let uu____1196 =
                                  FStar_SMTEncoding_Term.unboxBool x in
                                let uu____1197 =
                                  FStar_SMTEncoding_Term.unboxBool y in
                                (uu____1196, uu____1197) in
                              FStar_SMTEncoding_Util.mkAnd uu____1191 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1190 in
                          quant xy uu____1189 in
                        (FStar_Parser_Const.op_And, uu____1170) in
                      let uu____1214 =
                        let uu____1237 =
                          let uu____1258 =
                            let uu____1277 =
                              let uu____1278 =
                                let uu____1279 =
                                  let uu____1284 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  let uu____1285 =
                                    FStar_SMTEncoding_Term.unboxBool y in
                                  (uu____1284, uu____1285) in
                                FStar_SMTEncoding_Util.mkOr uu____1279 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1278 in
                            quant xy uu____1277 in
                          (FStar_Parser_Const.op_Or, uu____1258) in
                        let uu____1302 =
                          let uu____1325 =
                            let uu____1346 =
                              let uu____1365 =
                                let uu____1366 =
                                  let uu____1367 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  FStar_SMTEncoding_Util.mkNot uu____1367 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1366 in
                              quant qx uu____1365 in
                            (FStar_Parser_Const.op_Negation, uu____1346) in
                          let uu____1384 =
                            let uu____1407 =
                              let uu____1428 =
                                let uu____1447 =
                                  let uu____1448 =
                                    let uu____1449 =
                                      let uu____1454 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____1455 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____1454, uu____1455) in
                                    FStar_SMTEncoding_Util.mkLT uu____1449 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1448 in
                                quant xy uu____1447 in
                              (FStar_Parser_Const.op_LT, uu____1428) in
                            let uu____1472 =
                              let uu____1495 =
                                let uu____1516 =
                                  let uu____1535 =
                                    let uu____1536 =
                                      let uu____1537 =
                                        let uu____1542 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____1543 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____1542, uu____1543) in
                                      FStar_SMTEncoding_Util.mkLTE uu____1537 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1536 in
                                  quant xy uu____1535 in
                                (FStar_Parser_Const.op_LTE, uu____1516) in
                              let uu____1560 =
                                let uu____1583 =
                                  let uu____1604 =
                                    let uu____1623 =
                                      let uu____1624 =
                                        let uu____1625 =
                                          let uu____1630 =
                                            FStar_SMTEncoding_Term.unboxInt x in
                                          let uu____1631 =
                                            FStar_SMTEncoding_Term.unboxInt y in
                                          (uu____1630, uu____1631) in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1625 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1624 in
                                    quant xy uu____1623 in
                                  (FStar_Parser_Const.op_GT, uu____1604) in
                                let uu____1648 =
                                  let uu____1671 =
                                    let uu____1692 =
                                      let uu____1711 =
                                        let uu____1712 =
                                          let uu____1713 =
                                            let uu____1718 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____1719 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____1718, uu____1719) in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1713 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1712 in
                                      quant xy uu____1711 in
                                    (FStar_Parser_Const.op_GTE, uu____1692) in
                                  let uu____1736 =
                                    let uu____1759 =
                                      let uu____1780 =
                                        let uu____1799 =
                                          let uu____1800 =
                                            let uu____1801 =
                                              let uu____1806 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____1807 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____1806, uu____1807) in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1801 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1800 in
                                        quant xy uu____1799 in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1780) in
                                    let uu____1824 =
                                      let uu____1847 =
                                        let uu____1868 =
                                          let uu____1887 =
                                            let uu____1888 =
                                              let uu____1889 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1889 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1888 in
                                          quant qx uu____1887 in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1868) in
                                      let uu____1906 =
                                        let uu____1929 =
                                          let uu____1950 =
                                            let uu____1969 =
                                              let uu____1970 =
                                                let uu____1971 =
                                                  let uu____1976 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____1977 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____1976, uu____1977) in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1971 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1970 in
                                            quant xy uu____1969 in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1950) in
                                        let uu____1994 =
                                          let uu____2017 =
                                            let uu____2038 =
                                              let uu____2057 =
                                                let uu____2058 =
                                                  let uu____2059 =
                                                    let uu____2064 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x in
                                                    let uu____2065 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y in
                                                    (uu____2064, uu____2065) in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2059 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2058 in
                                              quant xy uu____2057 in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2038) in
                                          let uu____2082 =
                                            let uu____2105 =
                                              let uu____2126 =
                                                let uu____2145 =
                                                  let uu____2146 =
                                                    let uu____2147 =
                                                      let uu____2152 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x in
                                                      let uu____2153 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y in
                                                      (uu____2152,
                                                        uu____2153) in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2147 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2146 in
                                                quant xy uu____2145 in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2126) in
                                            let uu____2170 =
                                              let uu____2193 =
                                                let uu____2214 =
                                                  let uu____2233 =
                                                    let uu____2234 =
                                                      let uu____2235 =
                                                        let uu____2240 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x in
                                                        let uu____2241 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y in
                                                        (uu____2240,
                                                          uu____2241) in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2235 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2234 in
                                                  quant xy uu____2233 in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2214) in
                                              let uu____2258 =
                                                let uu____2281 =
                                                  let uu____2302 =
                                                    let uu____2321 =
                                                      let uu____2322 =
                                                        let uu____2323 =
                                                          let uu____2328 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x in
                                                          let uu____2329 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y in
                                                          (uu____2328,
                                                            uu____2329) in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2323 in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2322 in
                                                    quant xy uu____2321 in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2302) in
                                                let uu____2346 =
                                                  let uu____2369 =
                                                    let uu____2390 =
                                                      let uu____2409 =
                                                        let uu____2410 =
                                                          let uu____2411 =
                                                            let uu____2416 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x in
                                                            let uu____2417 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y in
                                                            (uu____2416,
                                                              uu____2417) in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2411 in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2410 in
                                                      quant xy uu____2409 in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2390) in
                                                  let uu____2434 =
                                                    let uu____2457 =
                                                      let uu____2478 =
                                                        let uu____2497 =
                                                          let uu____2498 =
                                                            let uu____2499 =
                                                              let uu____2504
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x in
                                                              let uu____2505
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y in
                                                              (uu____2504,
                                                                uu____2505) in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2499 in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2498 in
                                                        quant xy uu____2497 in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2478) in
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
                                                                    x in
                                                                let uu____2593
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                (uu____2592,
                                                                  uu____2593) in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2587 in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2586 in
                                                          quant xy uu____2585 in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2566) in
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
                                                                    x in
                                                                  let uu____2681
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                  (uu____2680,
                                                                    uu____2681) in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2675 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2674 in
                                                            quant xy
                                                              uu____2673 in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2654) in
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
                                                                    x in
                                                                    let uu____2769
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2768,
                                                                    uu____2769) in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2763 in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2762 in
                                                              quant xy
                                                                uu____2761 in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2742) in
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
                                                                    x in
                                                                    let uu____2857
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2856,
                                                                    uu____2857) in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2851 in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2850 in
                                                                quant xy
                                                                  uu____2849 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2830) in
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
                                                                    x in
                                                                    let uu____2945
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2944,
                                                                    uu____2945) in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2939 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2938 in
                                                                  quant xy
                                                                    uu____2937 in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2918) in
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
                                                                    x in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____3027
                                                                    FStar_Range.dummyRange in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____3026 in
                                                                    quant qx
                                                                    uu____3025 in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____3006) in
                                                                [uu____2985] in
                                                              uu____2897 ::
                                                                uu____2962 in
                                                            uu____2809 ::
                                                              uu____2874 in
                                                          uu____2721 ::
                                                            uu____2786 in
                                                        uu____2633 ::
                                                          uu____2698 in
                                                      uu____2545 ::
                                                        uu____2610 in
                                                    uu____2457 :: uu____2522 in
                                                  uu____2369 :: uu____2434 in
                                                uu____2281 :: uu____2346 in
                                              uu____2193 :: uu____2258 in
                                            uu____2105 :: uu____2170 in
                                          uu____2017 :: uu____2082 in
                                        uu____1929 :: uu____1994 in
                                      uu____1847 :: uu____1906 in
                                    uu____1759 :: uu____1824 in
                                  uu____1671 :: uu____1736 in
                                uu____1583 :: uu____1648 in
                              uu____1495 :: uu____1560 in
                            uu____1407 :: uu____1472 in
                          uu____1325 :: uu____1384 in
                        uu____1237 :: uu____1302 in
                      uu____1149 :: uu____1214 in
                    uu____1067 :: uu____1126 in
                  uu____986 :: uu____1044 in
                let mk l v =
                  let uu____3566 =
                    let uu____3578 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____3668 ->
                              match uu____3668 with
                              | (l', uu____3689) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____3578
                      (FStar_Option.map
                         (fun uu____3788 ->
                            match uu____3788 with
                            | (uu____3816, b) ->
                                let uu____3850 = FStar_Ident.range_of_lid l in
                                b uu____3850 v)) in
                  FStar_All.pipe_right uu____3566 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____3933 ->
                          match uu____3933 with
                          | (l', uu____3954) -> FStar_Ident.lid_equals l l')) in
                { mk; is }))
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list
          -> FStar_SMTEncoding_Term.decl)
  =
  fun rng ->
    fun env ->
      fun tapp ->
        fun vars ->
          let uu____4028 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort in
          match uu____4028 with
          | (xxsym, xx) ->
              let uu____4039 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort in
              (match uu____4039 with
               | (ffsym, ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name in
                   let uu____4055 =
                     let uu____4063 =
                       let uu____4064 =
                         let uu____4075 =
                           let uu____4076 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort) in
                           let uu____4086 =
                             let uu____4097 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort) in
                             uu____4097 :: vars in
                           uu____4076 :: uu____4086 in
                         let uu____4123 =
                           let uu____4124 =
                             let uu____4129 =
                               let uu____4130 =
                                 let uu____4135 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx]) in
                                 (tapp, uu____4135) in
                               FStar_SMTEncoding_Util.mkEq uu____4130 in
                             (xx_has_type, uu____4129) in
                           FStar_SMTEncoding_Util.mkImp uu____4124 in
                         ([[xx_has_type]], uu____4075, uu____4123) in
                       FStar_SMTEncoding_Term.mkForall rng uu____4064 in
                     let uu____4148 =
                       let uu____4150 =
                         let uu____4152 =
                           let uu____4154 =
                             FStar_Util.digest_of_string tapp_hash in
                           Prims.op_Hat "_pretyping_" uu____4154 in
                         Prims.op_Hat module_name uu____4152 in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____4150 in
                     (uu____4063, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____4148) in
                   FStar_SMTEncoding_Util.mkAssume uu____4055)
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx =
    FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy =
    FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mkForall_fuel env =
    let uu____4210 =
      let uu____4212 = FStar_TypeChecker_Env.current_module env in
      FStar_Ident.string_of_lid uu____4212 in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4210 in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____4234 =
      let uu____4235 =
        let uu____4243 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____4243, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4235 in
    let uu____4248 =
      let uu____4251 =
        let uu____4252 =
          let uu____4260 =
            let uu____4261 =
              let uu____4272 =
                let uu____4273 =
                  let uu____4278 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____4278) in
                FStar_SMTEncoding_Util.mkImp uu____4273 in
              ([[typing_pred]], [xx], uu____4272) in
            let uu____4303 =
              let uu____4318 = FStar_TypeChecker_Env.get_range env in
              let uu____4319 = mkForall_fuel env in uu____4319 uu____4318 in
            uu____4303 uu____4261 in
          (uu____4260, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4252 in
      [uu____4251] in
    uu____4234 :: uu____4248 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____4366 =
      let uu____4367 =
        let uu____4375 =
          let uu____4376 = FStar_TypeChecker_Env.get_range env in
          let uu____4377 =
            let uu____4388 =
              let uu____4393 =
                let uu____4396 = FStar_SMTEncoding_Term.boxBool b in
                [uu____4396] in
              [uu____4393] in
            let uu____4401 =
              let uu____4402 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____4402 tt in
            (uu____4388, [bb], uu____4401) in
          FStar_SMTEncoding_Term.mkForall uu____4376 uu____4377 in
        (uu____4375, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4367 in
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
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____4457) in
                FStar_SMTEncoding_Util.mkImp uu____4452 in
              ([[typing_pred]], [xx], uu____4451) in
            let uu____4484 =
              let uu____4499 = FStar_TypeChecker_Env.get_range env in
              let uu____4500 = mkForall_fuel env in uu____4500 uu____4499 in
            uu____4484 uu____4440 in
          (uu____4439, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4431 in
      [uu____4430] in
    uu____4366 :: uu____4427 in
  let mk_int env nm tt =
    let lex_t =
      let uu____4543 =
        let uu____4544 =
          let uu____4550 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu____4550, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu____4544 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4543 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu____4564 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4564 in
    let uu____4569 =
      let uu____4570 =
        let uu____4578 =
          let uu____4579 = FStar_TypeChecker_Env.get_range env in
          let uu____4580 =
            let uu____4591 =
              let uu____4596 =
                let uu____4599 = FStar_SMTEncoding_Term.boxInt b in
                [uu____4599] in
              [uu____4596] in
            let uu____4604 =
              let uu____4605 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____4605 tt in
            (uu____4591, [bb], uu____4604) in
          FStar_SMTEncoding_Term.mkForall uu____4579 uu____4580 in
        (uu____4578, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4570 in
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
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____4660) in
                FStar_SMTEncoding_Util.mkImp uu____4655 in
              ([[typing_pred]], [xx], uu____4654) in
            let uu____4687 =
              let uu____4702 = FStar_TypeChecker_Env.get_range env in
              let uu____4703 = mkForall_fuel env in uu____4703 uu____4702 in
            uu____4687 uu____4643 in
          (uu____4642, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4634 in
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
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____4772 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero in
                                (uu____4771, uu____4772) in
                              FStar_SMTEncoding_Util.mkGT uu____4766 in
                            let uu____4774 =
                              let uu____4777 =
                                let uu____4778 =
                                  let uu____4783 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____4784 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero in
                                  (uu____4783, uu____4784) in
                                FStar_SMTEncoding_Util.mkGTE uu____4778 in
                              let uu____4786 =
                                let uu____4789 =
                                  let uu____4790 =
                                    let uu____4795 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____4796 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____4795, uu____4796) in
                                  FStar_SMTEncoding_Util.mkLT uu____4790 in
                                [uu____4789] in
                              uu____4777 :: uu____4786 in
                            uu____4765 :: uu____4774 in
                          typing_pred_y :: uu____4762 in
                        typing_pred :: uu____4759 in
                      FStar_SMTEncoding_Util.mk_and_l uu____4756 in
                    (uu____4755, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____4750 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4749) in
              let uu____4829 =
                let uu____4844 = FStar_TypeChecker_Env.get_range env in
                let uu____4845 = mkForall_fuel env in uu____4845 uu____4844 in
              uu____4829 uu____4738 in
            (uu____4737,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____4729 in
        [uu____4728] in
      uu____4633 :: uu____4725 in
    uu____4569 :: uu____4630 in
  let mk_real env nm tt =
    let lex_t =
      let uu____4888 =
        let uu____4889 =
          let uu____4895 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu____4895, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu____4889 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4888 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv
        ("a", (FStar_SMTEncoding_Term.Sort "Real")) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv
        ("b", (FStar_SMTEncoding_Term.Sort "Real")) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu____4911 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4911 in
    let uu____4916 =
      let uu____4917 =
        let uu____4925 =
          let uu____4926 = FStar_TypeChecker_Env.get_range env in
          let uu____4927 =
            let uu____4938 =
              let uu____4943 =
                let uu____4946 = FStar_SMTEncoding_Term.boxReal b in
                [uu____4946] in
              [uu____4943] in
            let uu____4951 =
              let uu____4952 = FStar_SMTEncoding_Term.boxReal b in
              FStar_SMTEncoding_Term.mk_HasType uu____4952 tt in
            (uu____4938, [bb], uu____4951) in
          FStar_SMTEncoding_Term.mkForall uu____4926 uu____4927 in
        (uu____4925, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4917 in
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
                         FStar_SMTEncoding_Term.boxRealFun) x in
                  (typing_pred, uu____5007) in
                FStar_SMTEncoding_Util.mkImp uu____5002 in
              ([[typing_pred]], [xx], uu____5001) in
            let uu____5034 =
              let uu____5049 = FStar_TypeChecker_Env.get_range env in
              let uu____5050 = mkForall_fuel env in uu____5050 uu____5049 in
            uu____5034 uu____4990 in
          (uu____4989, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4981 in
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
                                  FStar_SMTEncoding_Term.unboxReal x in
                                let uu____5119 =
                                  FStar_SMTEncoding_Util.mkReal "0.0" in
                                (uu____5118, uu____5119) in
                              FStar_SMTEncoding_Util.mkGT uu____5113 in
                            let uu____5121 =
                              let uu____5124 =
                                let uu____5125 =
                                  let uu____5130 =
                                    FStar_SMTEncoding_Term.unboxReal y in
                                  let uu____5131 =
                                    FStar_SMTEncoding_Util.mkReal "0.0" in
                                  (uu____5130, uu____5131) in
                                FStar_SMTEncoding_Util.mkGTE uu____5125 in
                              let uu____5133 =
                                let uu____5136 =
                                  let uu____5137 =
                                    let uu____5142 =
                                      FStar_SMTEncoding_Term.unboxReal y in
                                    let uu____5143 =
                                      FStar_SMTEncoding_Term.unboxReal x in
                                    (uu____5142, uu____5143) in
                                  FStar_SMTEncoding_Util.mkLT uu____5137 in
                                [uu____5136] in
                              uu____5124 :: uu____5133 in
                            uu____5112 :: uu____5121 in
                          typing_pred_y :: uu____5109 in
                        typing_pred :: uu____5106 in
                      FStar_SMTEncoding_Util.mk_and_l uu____5103 in
                    (uu____5102, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____5097 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____5096) in
              let uu____5176 =
                let uu____5191 = FStar_TypeChecker_Env.get_range env in
                let uu____5192 = mkForall_fuel env in uu____5192 uu____5191 in
              uu____5176 uu____5085 in
            (uu____5084,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real") in
          FStar_SMTEncoding_Util.mkAssume uu____5076 in
        [uu____5075] in
      uu____4980 :: uu____5072 in
    uu____4916 :: uu____4977 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____5239 =
      let uu____5240 =
        let uu____5248 =
          let uu____5249 = FStar_TypeChecker_Env.get_range env in
          let uu____5250 =
            let uu____5261 =
              let uu____5266 =
                let uu____5269 = FStar_SMTEncoding_Term.boxString b in
                [uu____5269] in
              [uu____5266] in
            let uu____5274 =
              let uu____5275 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____5275 tt in
            (uu____5261, [bb], uu____5274) in
          FStar_SMTEncoding_Term.mkForall uu____5249 uu____5250 in
        (uu____5248, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____5240 in
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
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____5330) in
                FStar_SMTEncoding_Util.mkImp uu____5325 in
              ([[typing_pred]], [xx], uu____5324) in
            let uu____5357 =
              let uu____5372 = FStar_TypeChecker_Env.get_range env in
              let uu____5373 = mkForall_fuel env in uu____5373 uu____5372 in
            uu____5357 uu____5313 in
          (uu____5312, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____5304 in
      [uu____5303] in
    uu____5239 :: uu____5300 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    let uu____5420 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp") in
    [uu____5420] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____5450 =
      let uu____5451 =
        let uu____5459 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____5459, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5451 in
    [uu____5450] in
  let mk_and_interp env conj uu____5482 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____5511 =
      let uu____5512 =
        let uu____5520 =
          let uu____5521 = FStar_TypeChecker_Env.get_range env in
          let uu____5522 =
            let uu____5533 =
              let uu____5534 =
                let uu____5539 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____5539, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5534 in
            ([[l_and_a_b]], [aa; bb], uu____5533) in
          FStar_SMTEncoding_Term.mkForall uu____5521 uu____5522 in
        (uu____5520, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5512 in
    [uu____5511] in
  let mk_or_interp env disj uu____5594 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____5623 =
      let uu____5624 =
        let uu____5632 =
          let uu____5633 = FStar_TypeChecker_Env.get_range env in
          let uu____5634 =
            let uu____5645 =
              let uu____5646 =
                let uu____5651 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____5651, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5646 in
            ([[l_or_a_b]], [aa; bb], uu____5645) in
          FStar_SMTEncoding_Term.mkForall uu____5633 uu____5634 in
        (uu____5632, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5624 in
    [uu____5623] in
  let mk_eq2_interp env eq2 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____5729 =
      let uu____5730 =
        let uu____5738 =
          let uu____5739 = FStar_TypeChecker_Env.get_range env in
          let uu____5740 =
            let uu____5751 =
              let uu____5752 =
                let uu____5757 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____5757, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5752 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5751) in
          FStar_SMTEncoding_Term.mkForall uu____5739 uu____5740 in
        (uu____5738, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5730 in
    [uu____5729] in
  let mk_eq3_interp env eq3 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____5847 =
      let uu____5848 =
        let uu____5856 =
          let uu____5857 = FStar_TypeChecker_Env.get_range env in
          let uu____5858 =
            let uu____5869 =
              let uu____5870 =
                let uu____5875 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____5875, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5870 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5869) in
          FStar_SMTEncoding_Term.mkForall uu____5857 uu____5858 in
        (uu____5856, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5848 in
    [uu____5847] in
  let mk_imp_interp env imp tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____5975 =
      let uu____5976 =
        let uu____5984 =
          let uu____5985 = FStar_TypeChecker_Env.get_range env in
          let uu____5986 =
            let uu____5997 =
              let uu____5998 =
                let uu____6003 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____6003, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5998 in
            ([[l_imp_a_b]], [aa; bb], uu____5997) in
          FStar_SMTEncoding_Term.mkForall uu____5985 uu____5986 in
        (uu____5984, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5976 in
    [uu____5975] in
  let mk_iff_interp env iff tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____6087 =
      let uu____6088 =
        let uu____6096 =
          let uu____6097 = FStar_TypeChecker_Env.get_range env in
          let uu____6098 =
            let uu____6109 =
              let uu____6110 =
                let uu____6115 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____6115, valid) in
              FStar_SMTEncoding_Util.mkIff uu____6110 in
            ([[l_iff_a_b]], [aa; bb], uu____6109) in
          FStar_SMTEncoding_Term.mkForall uu____6097 uu____6098 in
        (uu____6096, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____6088 in
    [uu____6087] in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____6186 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____6186 in
    let uu____6191 =
      let uu____6192 =
        let uu____6200 =
          let uu____6201 = FStar_TypeChecker_Env.get_range env in
          let uu____6202 =
            let uu____6213 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____6213) in
          FStar_SMTEncoding_Term.mkForall uu____6201 uu____6202 in
        (uu____6200, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____6192 in
    [uu____6191] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____6266 =
      let uu____6267 =
        let uu____6275 =
          let uu____6276 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____6276 range_ty in
        let uu____6277 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const" in
        (uu____6275, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____6277) in
      FStar_SMTEncoding_Util.mkAssume uu____6267 in
    [uu____6266] in
  let mk_inversion_axiom env inversion tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____6323 = FStar_SMTEncoding_Term.n_fuel Prims.int_one in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____6323 x1 t in
      let uu____6325 = FStar_TypeChecker_Env.get_range env in
      let uu____6326 =
        let uu____6337 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____6337) in
      FStar_SMTEncoding_Term.mkForall uu____6325 uu____6326 in
    let uu____6362 =
      let uu____6363 =
        let uu____6371 =
          let uu____6372 = FStar_TypeChecker_Env.get_range env in
          let uu____6373 =
            let uu____6384 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____6384) in
          FStar_SMTEncoding_Term.mkForall uu____6372 uu____6373 in
        (uu____6371,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____6363 in
    [uu____6362] in
  let mk_with_type_axiom env with_type tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type, [t; e]) in
    let uu____6445 =
      let uu____6446 =
        let uu____6454 =
          let uu____6455 = FStar_TypeChecker_Env.get_range env in
          let uu____6456 =
            let uu____6472 =
              let uu____6473 =
                let uu____6478 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____6479 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____6478, uu____6479) in
              FStar_SMTEncoding_Util.mkAnd uu____6473 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu____6472) in
          FStar_SMTEncoding_Term.mkForall' uu____6455 uu____6456 in
        (uu____6454,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____6446 in
    [uu____6445] in
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
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env ->
    fun t ->
      fun s ->
        fun tt ->
          let uu____7037 =
            FStar_Util.find_opt
              (fun uu____7075 ->
                 match uu____7075 with
                 | (l, uu____7091) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____7037 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (uu____7134, f) -> f env s tt
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env ->
    fun fv ->
      fun t ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____7195 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env in
        match uu____7195 with
        | (form, decls) ->
            let uu____7204 =
              let uu____7207 =
                let uu____7210 =
                  let uu____7211 =
                    let uu____7219 =
                      let uu____7220 =
                        let uu____7222 = FStar_Ident.string_of_lid lid in
                        Prims.op_Hat "Lemma: " uu____7222 in
                      FStar_Pervasives_Native.Some uu____7220 in
                    let uu____7226 =
                      let uu____7228 = FStar_Ident.string_of_lid lid in
                      Prims.op_Hat "lemma_" uu____7228 in
                    (form, uu____7219, uu____7226) in
                  FStar_SMTEncoding_Util.mkAssume uu____7211 in
                [uu____7210] in
              FStar_All.pipe_right uu____7207
                FStar_SMTEncoding_Term.mk_decls_trivial in
            FStar_List.append decls uu____7204
let (close_universes :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.fvs ->
      FStar_SMTEncoding_Term.pat ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun univ_fvs ->
      fun pat ->
        fun body ->
          FStar_SMTEncoding_Term.mkForall rng ([[pat]], univ_fvs, body)
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                (FStar_SMTEncoding_Term.decls_t *
                  FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted ->
    fun env ->
      fun fv ->
        fun us ->
          fun tt ->
            fun t_norm ->
              fun quals ->
                let lid =
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                let uu____7324 =
                  ((let uu____7328 =
                      (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                        (FStar_SMTEncoding_Util.is_smt_reifiable_function
                           env.FStar_SMTEncoding_Env.tcenv t_norm) in
                    FStar_All.pipe_left Prims.op_Negation uu____7328) ||
                     (FStar_Syntax_Util.is_lemma t_norm))
                    || uninterpreted in
                if uu____7324
                then
                  let arg_sorts =
                    let uu____7340 =
                      let uu____7341 = FStar_Syntax_Subst.compress t_norm in
                      uu____7341.FStar_Syntax_Syntax.n in
                    match uu____7340 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders, uu____7347) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____7385 ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____7392 -> [] in
                  let arity = FStar_List.length arg_sorts in
                  let uu____7394 =
                    FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                      env lid arity in
                  match uu____7394 with
                  | (vname, vtok, env1) ->
                      let univ_arity =
                        FStar_List.map
                          (fun uu____7418 -> FStar_SMTEncoding_Term.univ_sort)
                          us in
                      let d =
                        FStar_SMTEncoding_Term.DeclFun
                          (vname, (FStar_List.append univ_arity arg_sorts),
                            FStar_SMTEncoding_Term.Term_sort,
                            (FStar_Pervasives_Native.Some
                               "Uninterpreted function symbol for impure function")) in
                      let dd =
                        FStar_SMTEncoding_Term.DeclFun
                          (vtok, univ_arity,
                            FStar_SMTEncoding_Term.Term_sort,
                            (FStar_Pervasives_Native.Some
                               "Uninterpreted name for impure function")) in
                      let uu____7431 =
                        FStar_All.pipe_right [d; dd]
                          FStar_SMTEncoding_Term.mk_decls_trivial in
                      (uu____7431, env1)
                else
                  (let uu____7436 = prims.is lid in
                   if uu____7436
                   then
                     (if (FStar_List.length us) <> Prims.int_zero
                      then
                        failwith
                          "Impossible: unexpected universe-polymorphic primitive function"
                      else ();
                      (let vname =
                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                           lid in
                       let uu____7452 = prims.mk lid vname in
                       match uu____7452 with
                       | (tok, arity, definition) ->
                           let env1 =
                             FStar_SMTEncoding_Env.push_free_var env lid
                               arity vname (FStar_Pervasives_Native.Some tok) in
                           let uu____7476 =
                             FStar_All.pipe_right definition
                               FStar_SMTEncoding_Term.mk_decls_trivial in
                           (uu____7476, env1)))
                   else
                     (let encode_non_total_function_typ =
                        let uu____7483 = FStar_Ident.nsstr lid in
                        uu____7483 <> "Prims" in
                      let uu____7487 =
                        let uu____7506 =
                          FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                            t_norm in
                        match uu____7506 with
                        | (args, comp) ->
                            let comp1 =
                              let uu____7534 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                  env.FStar_SMTEncoding_Env.tcenv comp in
                              if uu____7534
                              then
                                let uu____7539 =
                                  FStar_TypeChecker_Env.reify_comp
                                    (let uu___325_7542 =
                                       env.FStar_SMTEncoding_Env.tcenv in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___325_7542.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___325_7542.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___325_7542.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___325_7542.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_sig =
                                         (uu___325_7542.FStar_TypeChecker_Env.gamma_sig);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___325_7542.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___325_7542.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___325_7542.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___325_7542.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.attrtab =
                                         (uu___325_7542.FStar_TypeChecker_Env.attrtab);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___325_7542.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___325_7542.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___325_7542.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___325_7542.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___325_7542.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___325_7542.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.use_eq_strict =
                                         (uu___325_7542.FStar_TypeChecker_Env.use_eq_strict);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___325_7542.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___325_7542.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax = true;
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___325_7542.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.phase1 =
                                         (uu___325_7542.FStar_TypeChecker_Env.phase1);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___325_7542.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___325_7542.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.uvar_subtyping =
                                         (uu___325_7542.FStar_TypeChecker_Env.uvar_subtyping);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___325_7542.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___325_7542.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___325_7542.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.check_type_of =
                                         (uu___325_7542.FStar_TypeChecker_Env.check_type_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         (uu___325_7542.FStar_TypeChecker_Env.use_bv_sorts);
                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.qtbl_name_and_index);
                                       FStar_TypeChecker_Env.normalized_eff_names
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.normalized_eff_names);
                                       FStar_TypeChecker_Env.fv_delta_depths
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.fv_delta_depths);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___325_7542.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth_hook =
                                         (uu___325_7542.FStar_TypeChecker_Env.synth_hook);
                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                       FStar_TypeChecker_Env.splice =
                                         (uu___325_7542.FStar_TypeChecker_Env.splice);
                                       FStar_TypeChecker_Env.mpreprocess =
                                         (uu___325_7542.FStar_TypeChecker_Env.mpreprocess);
                                       FStar_TypeChecker_Env.postprocess =
                                         (uu___325_7542.FStar_TypeChecker_Env.postprocess);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___325_7542.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___325_7542.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.nbe =
                                         (uu___325_7542.FStar_TypeChecker_Env.nbe);
                                       FStar_TypeChecker_Env.strict_args_tab
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.strict_args_tab);
                                       FStar_TypeChecker_Env.erasable_types_tab
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.erasable_types_tab);
                                       FStar_TypeChecker_Env.enable_defer_to_tac
                                         =
                                         (uu___325_7542.FStar_TypeChecker_Env.enable_defer_to_tac)
                                     }) comp FStar_Syntax_Syntax.U_unknown in
                                FStar_Syntax_Syntax.mk_Total uu____7539
                              else comp in
                            if encode_non_total_function_typ
                            then
                              let uu____7565 =
                                FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                  env.FStar_SMTEncoding_Env.tcenv comp1 in
                              (args, uu____7565)
                            else
                              (args,
                                (FStar_Pervasives_Native.None,
                                  (FStar_Syntax_Util.comp_result comp1))) in
                      match uu____7487 with
                      | (formals, (pre_opt, res_t)) ->
                          let mk_disc_proj_axioms guard encoded_res_t vapp
                            vars =
                            FStar_All.pipe_right quals
                              (FStar_List.collect
                                 (fun uu___0_7671 ->
                                    match uu___0_7671 with
                                    | FStar_Syntax_Syntax.Discriminator d ->
                                        let uu____7675 =
                                          FStar_Util.prefix vars in
                                        (match uu____7675 with
                                         | (uu____7708, xxv) ->
                                             let xx =
                                               let uu____7747 =
                                                 let uu____7748 =
                                                   let uu____7754 =
                                                     FStar_SMTEncoding_Term.fv_name
                                                       xxv in
                                                   (uu____7754,
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 FStar_SMTEncoding_Term.mk_fv
                                                   uu____7748 in
                                               FStar_All.pipe_left
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 uu____7747 in
                                             let uu____7757 =
                                               let uu____7758 =
                                                 let uu____7766 =
                                                   let uu____7767 =
                                                     FStar_Syntax_Syntax.range_of_fv
                                                       fv in
                                                   let uu____7768 =
                                                     let uu____7779 =
                                                       let uu____7780 =
                                                         let uu____7785 =
                                                           let uu____7786 =
                                                             let uu____7787 =
                                                               let uu____7789
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   d in
                                                               FStar_SMTEncoding_Env.escape
                                                                 uu____7789 in
                                                             FStar_SMTEncoding_Term.mk_tester
                                                               uu____7787 xx in
                                                           FStar_All.pipe_left
                                                             FStar_SMTEncoding_Term.boxBool
                                                             uu____7786 in
                                                         (vapp, uu____7785) in
                                                       FStar_SMTEncoding_Util.mkEq
                                                         uu____7780 in
                                                     ([[vapp]], vars,
                                                       uu____7779) in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____7767 uu____7768 in
                                                 let uu____7799 =
                                                   let uu____7801 =
                                                     let uu____7803 =
                                                       FStar_Ident.string_of_lid
                                                         d in
                                                     FStar_SMTEncoding_Env.escape
                                                       uu____7803 in
                                                   Prims.op_Hat
                                                     "disc_equation_"
                                                     uu____7801 in
                                                 (uu____7766,
                                                   (FStar_Pervasives_Native.Some
                                                      "Discriminator equation"),
                                                   uu____7799) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____7758 in
                                             [uu____7757])
                                    | FStar_Syntax_Syntax.Projector (d, f) ->
                                        let uu____7811 =
                                          FStar_Util.prefix vars in
                                        (match uu____7811 with
                                         | (uu____7844, xxv) ->
                                             let xx =
                                               let uu____7883 =
                                                 let uu____7884 =
                                                   let uu____7890 =
                                                     FStar_SMTEncoding_Term.fv_name
                                                       xxv in
                                                   (uu____7890,
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 FStar_SMTEncoding_Term.mk_fv
                                                   uu____7884 in
                                               FStar_All.pipe_left
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 uu____7883 in
                                             let f1 =
                                               {
                                                 FStar_Syntax_Syntax.ppname =
                                                   f;
                                                 FStar_Syntax_Syntax.index =
                                                   Prims.int_zero;
                                                 FStar_Syntax_Syntax.sort =
                                                   FStar_Syntax_Syntax.tun
                                               } in
                                             let tp_name =
                                               FStar_SMTEncoding_Env.mk_term_projector_name
                                                 d f1 in
                                             let prim_app =
                                               FStar_SMTEncoding_Util.mkApp
                                                 (tp_name, [xx]) in
                                             let uu____7901 =
                                               let uu____7902 =
                                                 let uu____7910 =
                                                   let uu____7911 =
                                                     FStar_Syntax_Syntax.range_of_fv
                                                       fv in
                                                   let uu____7912 =
                                                     let uu____7923 =
                                                       FStar_SMTEncoding_Util.mkEq
                                                         (vapp, prim_app) in
                                                     ([[vapp]], vars,
                                                       uu____7923) in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____7911 uu____7912 in
                                                 (uu____7910,
                                                   (FStar_Pervasives_Native.Some
                                                      "Projector equation"),
                                                   (Prims.op_Hat
                                                      "proj_equation_"
                                                      tp_name)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____7902 in
                                             [uu____7901])
                                    | uu____7936 -> [])) in
                          let uu____7937 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              FStar_Pervasives_Native.None formals env in
                          (match uu____7937 with
                           | (vars, guards, env', decls1, uu____7962) ->
                               let uu____7975 =
                                 match pre_opt with
                                 | FStar_Pervasives_Native.None ->
                                     let uu____7988 =
                                       FStar_SMTEncoding_Util.mk_and_l guards in
                                     (uu____7988, decls1)
                                 | FStar_Pervasives_Native.Some p ->
                                     let uu____7992 =
                                       FStar_SMTEncoding_EncodeTerm.encode_formula
                                         p env' in
                                     (match uu____7992 with
                                      | (g, ds) ->
                                          let uu____8005 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (g :: guards) in
                                          (uu____8005,
                                            (FStar_List.append decls1 ds))) in
                               (match uu____7975 with
                                | (guard, decls11) ->
                                    let dummy_var =
                                      FStar_SMTEncoding_Term.mk_fv
                                        ("@dummy",
                                          FStar_SMTEncoding_Term.dummy_sort) in
                                    let dummy_tm =
                                      FStar_SMTEncoding_Term.mkFreeV
                                        dummy_var FStar_Range.dummyRange in
                                    let should_thunk uu____8028 =
                                      let is_type t =
                                        let uu____8036 =
                                          let uu____8037 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____8037.FStar_Syntax_Syntax.n in
                                        match uu____8036 with
                                        | FStar_Syntax_Syntax.Tm_type
                                            uu____8041 -> true
                                        | uu____8043 -> false in
                                      let is_squash t =
                                        let uu____8052 =
                                          FStar_Syntax_Util.head_and_args t in
                                        match uu____8052 with
                                        | (head, uu____8071) ->
                                            let uu____8096 =
                                              let uu____8097 =
                                                FStar_Syntax_Util.un_uinst
                                                  head in
                                              uu____8097.FStar_Syntax_Syntax.n in
                                            (match uu____8096 with
                                             | FStar_Syntax_Syntax.Tm_fvar
                                                 fv1 ->
                                                 FStar_Syntax_Syntax.fv_eq_lid
                                                   fv1
                                                   FStar_Parser_Const.squash_lid
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 ({
                                                    FStar_Syntax_Syntax.ppname
                                                      = uu____8102;
                                                    FStar_Syntax_Syntax.index
                                                      = uu____8103;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      {
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_fvar
                                                          fv1;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8105;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8106;_};_},
                                                  uu____8107)
                                                 ->
                                                 FStar_Syntax_Syntax.fv_eq_lid
                                                   fv1
                                                   FStar_Parser_Const.unit_lid
                                             | uu____8115 -> false) in
                                      ((((let uu____8119 =
                                            FStar_Ident.nsstr lid in
                                          uu____8119 <> "Prims") &&
                                           ((FStar_List.length us) >
                                              Prims.int_zero))
                                          &&
                                          (let uu____8125 =
                                             FStar_All.pipe_right quals
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Logic) in
                                           Prims.op_Negation uu____8125))
                                         &&
                                         (let uu____8131 = is_squash t_norm in
                                          Prims.op_Negation uu____8131))
                                        &&
                                        (let uu____8134 = is_type t_norm in
                                         Prims.op_Negation uu____8134) in
                                    let uu____8136 =
                                      match vars with
                                      | [] when should_thunk () ->
                                          (true, [dummy_var])
                                      | uu____8195 -> (false, vars) in
                                    (match uu____8136 with
                                     | (thunked, vars1) ->
                                         let arity =
                                           FStar_List.length formals in
                                         let uu____8245 =
                                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                             env lid arity thunked in
                                         (match uu____8245 with
                                          | (vname, vtok_opt, env1) ->
                                              let get_vtok uu____8277 =
                                                FStar_Option.get vtok_opt in
                                              let uu____8279 =
                                                let uu____8296 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_EncodeTerm.encode_univ_name
                                                    us in
                                                FStar_All.pipe_right
                                                  uu____8296 FStar_List.unzip in
                                              (match uu____8279 with
                                               | (univ_fvs, univs) ->
                                                   let univ_sorts =
                                                     FStar_All.pipe_right
                                                       univs
                                                       (FStar_List.map
                                                          (fun uu____8399 ->
                                                             FStar_SMTEncoding_Term.univ_sort)) in
                                                   let vtok_tm =
                                                     match formals with
                                                     | [] when thunked ->
                                                         FStar_SMTEncoding_Util.mkApp
                                                           (vname,
                                                             [dummy_tm])
                                                     | [] when
                                                         Prims.op_Negation
                                                           thunked
                                                         ->
                                                         FStar_SMTEncoding_Util.mkApp
                                                           (vname, univs)
                                                     | uu____8419 ->
                                                         let uu____8428 =
                                                           let uu____8436 =
                                                             get_vtok () in
                                                           (uu____8436,
                                                             univs) in
                                                         FStar_SMTEncoding_Util.mkApp
                                                           uu____8428 in
                                                   let vtok_app =
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm vars1 in
                                                   let vapp =
                                                     let uu____8443 =
                                                       let uu____8451 =
                                                         let uu____8454 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             vars1 in
                                                         FStar_List.append
                                                           univs uu____8454 in
                                                       (vname, uu____8451) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8443 in
                                                   let uu____8468 =
                                                     let vname_decl =
                                                       let uu____8476 =
                                                         let uu____8488 =
                                                           let uu____8491 =
                                                             FStar_All.pipe_right
                                                               vars1
                                                               (FStar_List.map
                                                                  FStar_SMTEncoding_Term.fv_sort) in
                                                           FStar_List.append
                                                             univ_sorts
                                                             uu____8491 in
                                                         (vname, uu____8488,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None) in
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         uu____8476 in
                                                     let uu____8502 =
                                                       let env2 =
                                                         let uu___425_8508 =
                                                           env1 in
                                                         {
                                                           FStar_SMTEncoding_Env.bvar_bindings
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.bvar_bindings);
                                                           FStar_SMTEncoding_Env.fvar_bindings
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.fvar_bindings);
                                                           FStar_SMTEncoding_Env.depth
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.depth);
                                                           FStar_SMTEncoding_Env.tcenv
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.tcenv);
                                                           FStar_SMTEncoding_Env.warn
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.warn);
                                                           FStar_SMTEncoding_Env.nolabels
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.nolabels);
                                                           FStar_SMTEncoding_Env.use_zfuel_name
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.use_zfuel_name);
                                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                             =
                                                             encode_non_total_function_typ;
                                                           FStar_SMTEncoding_Env.current_module_name
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.current_module_name);
                                                           FStar_SMTEncoding_Env.encoding_quantifier
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.encoding_quantifier);
                                                           FStar_SMTEncoding_Env.global_cache
                                                             =
                                                             (uu___425_8508.FStar_SMTEncoding_Env.global_cache)
                                                         } in
                                                       let uu____8509 =
                                                         let uu____8511 =
                                                           FStar_SMTEncoding_EncodeTerm.head_normal
                                                             env2 tt in
                                                         Prims.op_Negation
                                                           uu____8511 in
                                                       if uu____8509
                                                       then
                                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           tt env2 vtok_tm
                                                       else
                                                         FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           t_norm env2
                                                           vtok_tm in
                                                     match uu____8502 with
                                                     | (tok_typing, decls2)
                                                         ->
                                                         let tok_typing1 =
                                                           let uu____8529 =
                                                             FStar_Syntax_Syntax.range_of_fv
                                                               fv in
                                                           close_universes
                                                             uu____8529
                                                             univ_fvs vtok_tm
                                                             tok_typing in
                                                         let uu____8530 =
                                                           match vars1 with
                                                           | [] ->
                                                               let tok_typing2
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "function token typing"),
                                                                    (Prims.op_Hat
                                                                    "function_token_typing_"
                                                                    vname)) in
                                                               let uu____8556
                                                                 =
                                                                 let uu____8559
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    [tok_typing2]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                 FStar_List.append
                                                                   decls2
                                                                   uu____8559 in
                                                               let uu____8566
                                                                 =
                                                                 let uu____8567
                                                                   =
                                                                   let uu____8570
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (vname,
                                                                    []) in
                                                                   FStar_All.pipe_left
                                                                    (fun
                                                                    uu____8576
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8576)
                                                                    uu____8570 in
                                                                 FStar_SMTEncoding_Env.push_free_var
                                                                   env1 lid
                                                                   arity
                                                                   vname
                                                                   uu____8567 in
                                                               (uu____8556,
                                                                 uu____8566)
                                                           | uu____8579 when
                                                               thunked ->
                                                               (decls2, env1)
                                                           | uu____8592 ->
                                                               let vtok =
                                                                 get_vtok () in
                                                               let vtok_decl
                                                                 =
                                                                 FStar_SMTEncoding_Term.DeclFun
                                                                   (vtok,
                                                                    univ_sorts,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    FStar_Pervasives_Native.None) in
                                                               let name_tok_corr_formula
                                                                 pat =
                                                                 let uu____8616
                                                                   =
                                                                   FStar_Syntax_Syntax.range_of_fv
                                                                    fv in
                                                                 let uu____8617
                                                                   =
                                                                   let uu____8628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (vtok_app,
                                                                    vapp) in
                                                                   ([[pat]],
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    vars1),
                                                                    uu____8628) in
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   uu____8616
                                                                   uu____8617 in
                                                               let name_tok_corr
                                                                 =
                                                                 let uu____8646
                                                                   =
                                                                   let uu____8654
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vtok_app in
                                                                   (uu____8654,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Name-token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    vname)) in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____8646 in
                                                               let tok_typing2
                                                                 =
                                                                 let guarded_tok_typing
                                                                   =
                                                                   match univ_fvs
                                                                   with
                                                                   | 
                                                                   uu____8661::uu____8662
                                                                    ->
                                                                    tok_typing1
                                                                   | 
                                                                   uu____8689
                                                                    ->
                                                                    let ff =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    ("ty",
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let f =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    ff in
                                                                    let vtok_app_r
                                                                    =
                                                                    let uu____8705
                                                                    =
                                                                    let uu____8706
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    [uu____8706] in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    f
                                                                    uu____8705 in
                                                                    let uu____8732
                                                                    =
                                                                    FStar_Syntax_Syntax.range_of_fv
                                                                    fv in
                                                                    let uu____8733
                                                                    =
                                                                    let uu____8744
                                                                    =
                                                                    let uu____8745
                                                                    =
                                                                    let uu____8750
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing1 in
                                                                    let uu____8751
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp in
                                                                    (uu____8750,
                                                                    uu____8751) in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____8745 in
                                                                    ([
                                                                    [vtok_app_r]],
                                                                    [ff],
                                                                    uu____8744) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8732
                                                                    uu____8733 in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   (guarded_tok_typing,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "function token typing"),
                                                                    (Prims.op_Hat
                                                                    "function_token_typing_"
                                                                    vname)) in
                                                               let uu____8780
                                                                 =
                                                                 let uu____8783
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    [vtok_decl;
                                                                    name_tok_corr;
                                                                    tok_typing2]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                 FStar_List.append
                                                                   decls2
                                                                   uu____8783 in
                                                               (uu____8780,
                                                                 env1) in
                                                         (match uu____8530
                                                          with
                                                          | (tok_decl, env2)
                                                              ->
                                                              let uu____8804
                                                                =
                                                                let uu____8807
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    [vname_decl]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                FStar_List.append
                                                                  uu____8807
                                                                  tok_decl in
                                                              (uu____8804,
                                                                env2)) in
                                                   (match uu____8468 with
                                                    | (decls2, env2) ->
                                                        let uu____8826 =
                                                          let res_t1 =
                                                            FStar_Syntax_Subst.compress
                                                              res_t in
                                                          let uu____8836 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              res_t1 env' in
                                                          match uu____8836
                                                          with
                                                          | (encoded_res_t,
                                                             decls) ->
                                                              let uu____8851
                                                                =
                                                                FStar_SMTEncoding_Term.mk_HasType
                                                                  vapp
                                                                  encoded_res_t in
                                                              (encoded_res_t,
                                                                uu____8851,
                                                                decls) in
                                                        (match uu____8826
                                                         with
                                                         | (encoded_res_t,
                                                            ty_pred, decls3)
                                                             ->
                                                             let typingAx =
                                                               let uu____8866
                                                                 =
                                                                 let uu____8874
                                                                   =
                                                                   let uu____8875
                                                                    =
                                                                    FStar_Syntax_Syntax.range_of_fv
                                                                    fv in
                                                                   let uu____8876
                                                                    =
                                                                    let uu____8887
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    ty_pred) in
                                                                    ([[vapp]],
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    vars1),
                                                                    uu____8887) in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____8875
                                                                    uu____8876 in
                                                                 (uu____8874,
                                                                   (FStar_Pervasives_Native.Some
                                                                    "free var typing"),
                                                                   (Prims.op_Hat
                                                                    "typing_"
                                                                    vname)) in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____8866 in
                                                             let freshness =
                                                               let uu____8911
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   quals
                                                                   (FStar_List.contains
                                                                    FStar_Syntax_Syntax.New) in
                                                               if uu____8911
                                                               then
                                                                 let uu____8919
                                                                   =
                                                                   let uu____8920
                                                                    =
                                                                    FStar_Syntax_Syntax.range_of_fv
                                                                    fv in
                                                                   let uu____8921
                                                                    =
                                                                    let uu____8934
                                                                    =
                                                                    let uu____8937
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars1
                                                                    (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort) in
                                                                    FStar_List.append
                                                                    univ_sorts
                                                                    uu____8937 in
                                                                    let uu____8944
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                    () in
                                                                    (vname,
                                                                    uu____8934,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____8944) in
                                                                   FStar_SMTEncoding_Term.fresh_constructor
                                                                    uu____8920
                                                                    uu____8921 in
                                                                 let uu____8950
                                                                   =
                                                                   let uu____8953
                                                                    =
                                                                    let uu____8954
                                                                    =
                                                                    FStar_Syntax_Syntax.range_of_fv
                                                                    fv in
                                                                    pretype_axiom
                                                                    uu____8954
                                                                    env2 vapp
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    vars1) in
                                                                   [uu____8953] in
                                                                 uu____8919
                                                                   ::
                                                                   uu____8950
                                                               else [] in
                                                             let g =
                                                               let uu____8968
                                                                 =
                                                                 let uu____8971
                                                                   =
                                                                   let uu____8974
                                                                    =
                                                                    let uu____8977
                                                                    =
                                                                    let uu____8980
                                                                    =
                                                                    let uu____8983
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1 in
                                                                    typingAx
                                                                    ::
                                                                    uu____8983 in
                                                                    FStar_List.append
                                                                    freshness
                                                                    uu____8980 in
                                                                    FStar_All.pipe_right
                                                                    uu____8977
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                   FStar_List.append
                                                                    decls3
                                                                    uu____8974 in
                                                                 FStar_List.append
                                                                   decls2
                                                                   uu____8971 in
                                                               FStar_List.append
                                                                 decls11
                                                                 uu____8968 in
                                                             (g, env2))))))))))
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_SMTEncoding_Env.fvar_binding *
              FStar_SMTEncoding_Term.decls_elt Prims.list *
              FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun x ->
      fun us ->
        fun t ->
          fun t_norm ->
            let uu____9032 =
              FStar_SMTEncoding_Env.lookup_fvar_binding env
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____9032 with
            | FStar_Pervasives_Native.None ->
                let uu____9043 = encode_free_var false env x us t t_norm [] in
                (match uu____9043 with
                 | (decls, env1) ->
                     let fvb =
                       FStar_SMTEncoding_Env.lookup_lid env1
                         (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                     (fvb, decls, env1))
            | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
let (encode_top_level_val :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted ->
    fun env ->
      fun lid ->
        fun us ->
          fun t ->
            fun quals ->
              let tt = norm_before_encoding env t in
              let uu____9115 =
                encode_free_var uninterpreted env lid us t tt quals in
              match uu____9115 with
              | (decls, env1) ->
                  let uu____9126 = FStar_Syntax_Util.is_smt_lemma t in
                  if uu____9126
                  then
                    let uu____9133 =
                      let uu____9134 = encode_smt_lemma env1 lid tt in
                      FStar_List.append decls uu____9134 in
                    (uu____9133, env1)
                  else (decls, env1)
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_elt Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      fun quals ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____9193 ->
                fun lb ->
                  match uu____9193 with
                  | (decls, env1) ->
                      let uu____9213 =
                        FStar_Syntax_Subst.open_univ_vars
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp in
                      (match uu____9213 with
                       | (us, t) ->
                           let uu____9226 =
                             let uu____9231 =
                               FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                             encode_top_level_val false env1 uu____9231 us t
                               quals in
                           (match uu____9226 with
                            | (decls', env2) ->
                                ((FStar_List.append decls decls'), env2))))
             ([], env))
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____9260 = FStar_Syntax_Util.head_and_args t in
    match uu____9260 with
    | (hd, args) ->
        let uu____9304 =
          let uu____9305 = FStar_Syntax_Util.un_uinst hd in
          uu____9305.FStar_Syntax_Syntax.n in
        (match uu____9304 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____9311, c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             let uu____9334 = FStar_Ident.string_of_lid effect_name in
             FStar_Util.starts_with "FStar.Tactics" uu____9334
         | uu____9337 -> false)
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Let_rec_unencodeable -> true | uu____9348 -> false
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en ->
    let uu___519_9356 = en in
    let uu____9357 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___519_9356.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___519_9356.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___519_9356.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___519_9356.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___519_9356.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___519_9356.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___519_9356.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___519_9356.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___519_9356.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___519_9356.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9357
    }
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun uu____9387 ->
      fun quals ->
        match uu____9387 with
        | (is_rec, bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____9490 = FStar_Util.first_N nbinders formals in
              match uu____9490 with
              | (formals1, extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____9585 ->
                         fun uu____9586 ->
                           match (uu____9585, uu____9586) with
                           | ((formal, uu____9612), (binder, uu____9614)) ->
                               let uu____9635 =
                                 let uu____9642 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____9642) in
                               FStar_Syntax_Syntax.NT uu____9635) formals1
                      binders in
                  let extra_formals1 =
                    let uu____9656 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9697 ->
                              match uu____9697 with
                              | (x, i) ->
                                  let uu____9716 =
                                    let uu___545_9717 = x in
                                    let uu____9718 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___545_9717.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___545_9717.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9718
                                    } in
                                  (uu____9716, i))) in
                    FStar_All.pipe_right uu____9656
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____9740 = FStar_Syntax_Subst.compress body in
                    let uu____9741 =
                      let uu____9742 =
                        FStar_Syntax_Util.args_of_binders extra_formals1 in
                      FStar_All.pipe_left FStar_Pervasives_Native.snd
                        uu____9742 in
                    FStar_Syntax_Syntax.extend_app_n uu____9740 uu____9741
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function t e =
              let tcenv =
                let uu___552_9789 = env.FStar_SMTEncoding_Env.tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___552_9789.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___552_9789.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___552_9789.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___552_9789.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___552_9789.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___552_9789.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___552_9789.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___552_9789.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___552_9789.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___552_9789.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___552_9789.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___552_9789.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___552_9789.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___552_9789.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___552_9789.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___552_9789.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___552_9789.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___552_9789.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___552_9789.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___552_9789.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___552_9789.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___552_9789.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___552_9789.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___552_9789.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___552_9789.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___552_9789.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___552_9789.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___552_9789.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___552_9789.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___552_9789.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___552_9789.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___552_9789.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___552_9789.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___552_9789.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___552_9789.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___552_9789.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___552_9789.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___552_9789.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___552_9789.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___552_9789.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___552_9789.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___552_9789.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___552_9789.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___552_9789.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___552_9789.FStar_TypeChecker_Env.erasable_types_tab);
                  FStar_TypeChecker_Env.enable_defer_to_tac =
                    (uu___552_9789.FStar_TypeChecker_Env.enable_defer_to_tac)
                } in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu____9861 ->
                       fun uu____9862 ->
                         match (uu____9861, uu____9862) with
                         | ((x, uu____9888), (b, uu____9890)) ->
                             let uu____9911 =
                               let uu____9918 =
                                 FStar_Syntax_Syntax.bv_to_name b in
                               (x, uu____9918) in
                             FStar_Syntax_Syntax.NT uu____9911) formals
                    actuals in
                FStar_Syntax_Subst.subst_comp subst comp in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu____9943 = FStar_Syntax_Subst.compress t1 in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9943 in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals, comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9972 ->
                    let uu____9979 = FStar_Syntax_Util.unrefine t2 in
                    arrow_formals_comp_norm norm uu____9979
                | uu____9980 when Prims.op_Negation norm ->
                    let t_norm =
                      norm_with_steps
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Exclude
                          FStar_TypeChecker_Env.Zeta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] tcenv t2 in
                    arrow_formals_comp_norm true t_norm
                | uu____9983 ->
                    let uu____9984 = FStar_Syntax_Syntax.mk_Total t2 in
                    ([], uu____9984) in
              let aux t1 e1 =
                let uu____10026 = FStar_Syntax_Util.abs_formals e1 in
                match uu____10026 with
                | (binders, body, lopt) ->
                    let uu____10058 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____10074 -> arrow_formals_comp_norm false t1 in
                    (match uu____10058 with
                     | (formals, comp) ->
                         let nformals = FStar_List.length formals in
                         let nbinders = FStar_List.length binders in
                         let uu____10108 =
                           if nformals < nbinders
                           then
                             let uu____10142 =
                               FStar_Util.first_N nformals binders in
                             match uu____10142 with
                             | (bs0, rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt in
                                 let uu____10222 =
                                   subst_comp formals bs0 comp in
                                 (bs0, body1, uu____10222)
                           else
                             if nformals > nbinders
                             then
                               (let uu____10252 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp) in
                                match uu____10252 with
                                | (binders1, body1) ->
                                    let uu____10299 =
                                      subst_comp formals binders1 comp in
                                    (binders1, body1, uu____10299))
                             else
                               (let uu____10312 =
                                  subst_comp formals binders comp in
                                (binders, body, uu____10312)) in
                         (match uu____10108 with
                          | (binders1, body1, comp1) ->
                              (binders1, body1, comp1))) in
              let uu____10372 = aux t e in
              match uu____10372 with
              | (binders, body, comp) ->
                  let uu____10418 =
                    let uu____10429 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp in
                    if uu____10429
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body in
                      let uu____10444 = aux comp1 body1 in
                      match uu____10444 with
                      | (more_binders, body2, comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp) in
                  (match uu____10418 with
                   | (binders1, body1, comp1) ->
                       let uu____10527 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None) in
                       (binders1, uu____10527, comp1)) in
            (try
               (fun uu___622_10554 ->
                  match () with
                  | () ->
                      let uu____10561 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
                      if uu____10561
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10577 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10643 ->
                                   fun lb ->
                                     match uu____10643 with
                                     | (toks, typs, decls, env1) ->
                                         ((let uu____10698 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           if uu____10698
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let uu____10703 =
                                             FStar_Syntax_Subst.open_univ_vars
                                               lb.FStar_Syntax_Syntax.lbunivs
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           match uu____10703 with
                                           | (us, t) ->
                                               let t_norm =
                                                 norm_before_encoding env1 t in
                                               let uu____10727 =
                                                 let uu____10736 =
                                                   FStar_Util.right
                                                     lb.FStar_Syntax_Syntax.lbname in
                                                 declare_top_level_let env1
                                                   uu____10736 us t t_norm in
                                               (match uu____10727 with
                                                | (tok, decl, env2) ->
                                                    ((tok :: toks), (t_norm
                                                      :: typs), (decl ::
                                                      decls), env2)))))
                                ([], [], [], env)) in
                         match uu____10577 with
                         | (toks, typs, decls, env1) ->
                             let toks_fvbs = FStar_List.rev toks in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten in
                             let env_decls = copy_env env1 in
                             let typs1 = FStar_List.rev typs in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____10877;
                                    FStar_Syntax_Syntax.lbeff = uu____10878;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10880;
                                    FStar_Syntax_Syntax.lbpos = uu____10881;_}::[],
                                  t_norm::[], fvb::[]) ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid in
                                   let uu____10905 =
                                     let uu____10912 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm] in
                                     match uu____10912 with
                                     | (tcenv', uu____10928, e_t) ->
                                         let uu____10934 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10945 ->
                                               failwith "Impossible" in
                                         (match uu____10934 with
                                          | (e1, t_norm1) ->
                                              ((let uu___688_10962 = env2 in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___688_10962.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1)) in
                                   (match uu____10905 with
                                    | (env', e1, t_norm1) ->
                                        let uu____10972 =
                                          destruct_bound_function t_norm1 e1 in
                                        (match uu____10972 with
                                         | (binders, body, t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp in
                                             ((let uu____10992 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____10992
                                               then
                                                 let uu____10997 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____11000 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10997 uu____11000
                                               else ());
                                              (let uu____11005 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____11005 with
                                               | (vars, _guards, env'1,
                                                  binder_decls, uu____11032)
                                                   ->
                                                   let uu____11045 =
                                                     if
                                                       fvb.FStar_SMTEncoding_Env.fvb_thunked
                                                         && (vars = [])
                                                     then
                                                       let dummy_var =
                                                         FStar_SMTEncoding_Term.mk_fv
                                                           ("@dummy",
                                                             FStar_SMTEncoding_Term.dummy_sort) in
                                                       let dummy_tm =
                                                         FStar_SMTEncoding_Term.mkFreeV
                                                           dummy_var
                                                           FStar_Range.dummyRange in
                                                       let app =
                                                         let uu____11062 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____11062 in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____11084 =
                                                          let uu____11085 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn in
                                                          let uu____11086 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____11085 fvb
                                                            uu____11086 in
                                                        (vars, uu____11084)) in
                                                   (match uu____11045 with
                                                    | (vars1, app) ->
                                                        let uu____11097 =
                                                          let is_logical =
                                                            let uu____11110 =
                                                              let uu____11111
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body in
                                                              uu____11111.FStar_Syntax_Syntax.n in
                                                            match uu____11110
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____11117 ->
                                                                false in
                                                          let is_prims =
                                                            let uu____11121 =
                                                              let uu____11122
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right in
                                                              FStar_All.pipe_right
                                                                uu____11122
                                                                FStar_Syntax_Syntax.lid_of_fv in
                                                            FStar_All.pipe_right
                                                              uu____11121
                                                              (fun lid ->
                                                                 let uu____11131
                                                                   =
                                                                   let uu____11132
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu____11132 in
                                                                 FStar_Ident.lid_equals
                                                                   uu____11131
                                                                   FStar_Parser_Const.prims_lid) in
                                                          let uu____11133 =
                                                            (Prims.op_Negation
                                                               is_prims)
                                                              &&
                                                              ((FStar_All.pipe_right
                                                                  quals
                                                                  (FStar_List.contains
                                                                    FStar_Syntax_Syntax.Logic))
                                                                 ||
                                                                 is_logical) in
                                                          if uu____11133
                                                          then
                                                            let uu____11149 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app in
                                                            let uu____11150 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1 in
                                                            (app,
                                                              uu____11149,
                                                              uu____11150)
                                                          else
                                                            (let uu____11161
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1 in
                                                             (app, app,
                                                               uu____11161)) in
                                                        (match uu____11097
                                                         with
                                                         | (pat, app1,
                                                            (body1, decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____11185
                                                                 =
                                                                 let uu____11193
                                                                   =
                                                                   let uu____11194
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                   let uu____11195
                                                                    =
                                                                    let uu____11206
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1) in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____11206) in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____11194
                                                                    uu____11195 in
                                                                 let uu____11215
                                                                   =
                                                                   let uu____11216
                                                                    =
                                                                    let uu____11218
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu____11218 in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____11216 in
                                                                 (uu____11193,
                                                                   uu____11215,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id)) in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____11185 in
                                                             let uu____11224
                                                               =
                                                               let uu____11227
                                                                 =
                                                                 let uu____11230
                                                                   =
                                                                   let uu____11233
                                                                    =
                                                                    let uu____11236
                                                                    =
                                                                    let uu____11239
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1 in
                                                                    eqn ::
                                                                    uu____11239 in
                                                                    FStar_All.pipe_right
                                                                    uu____11236
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____11233 in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____11230 in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____11227 in
                                                             (uu____11224,
                                                               env2)))))))
                               | uu____11248 -> failwith "Impossible" in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____11308 =
                                   let uu____11314 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel" in
                                   (uu____11314,
                                     FStar_SMTEncoding_Term.Fuel_sort) in
                                 FStar_SMTEncoding_Term.mk_fv uu____11308 in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel in
                               let env0 = env2 in
                               let uu____11320 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11373 ->
                                         fun fvb ->
                                           match uu____11373 with
                                           | (gtoks, env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid in
                                               let g =
                                                 let uu____11428 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11428 in
                                               let gtok =
                                                 let uu____11432 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11432 in
                                               let env4 =
                                                 let uu____11435 =
                                                   let uu____11438 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm]) in
                                                   FStar_All.pipe_left
                                                     (fun uu____11444 ->
                                                        FStar_Pervasives_Native.Some
                                                          uu____11444)
                                                     uu____11438 in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11435 in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2)) in
                               match uu____11320 with
                               | (gtoks, env3) ->
                                   let gtoks1 = FStar_List.rev gtoks in
                                   let encode_one_binding env01 uu____11564
                                     t_norm uu____11566 =
                                     match (uu____11564, uu____11566) with
                                     | ((fvb, g, gtok),
                                        { FStar_Syntax_Syntax.lbname = lbn;
                                          FStar_Syntax_Syntax.lbunivs = uvs;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____11596;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____11597;
                                          FStar_Syntax_Syntax.lbdef = e;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____11599;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____11600;_})
                                         ->
                                         let uu____11627 =
                                           let uu____11634 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm] in
                                           match uu____11634 with
                                           | (tcenv', uu____11650, e_t) ->
                                               let uu____11656 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11667 ->
                                                     failwith "Impossible" in
                                               (match uu____11656 with
                                                | (e1, t_norm1) ->
                                                    ((let uu___775_11684 =
                                                        env3 in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___775_11684.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1)) in
                                         (match uu____11627 with
                                          | (env', e1, t_norm1) ->
                                              ((let uu____11697 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding") in
                                                if uu____11697
                                                then
                                                  let uu____11702 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn in
                                                  let uu____11704 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1 in
                                                  let uu____11706 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1 in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11702 uu____11704
                                                    uu____11706
                                                else ());
                                               (let uu____11711 =
                                                  destruct_bound_function
                                                    t_norm1 e1 in
                                                match uu____11711 with
                                                | (binders, body, tres_comp)
                                                    ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders) in
                                                    let uu____11738 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp in
                                                    (match uu____11738 with
                                                     | (pre_opt, tres) ->
                                                         ((let uu____11760 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify") in
                                                           if uu____11760
                                                           then
                                                             let uu____11765
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn in
                                                             let uu____11767
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders in
                                                             let uu____11770
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body in
                                                             let uu____11772
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11765
                                                               uu____11767
                                                               uu____11770
                                                               uu____11772
                                                           else ());
                                                          (let uu____11777 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env' in
                                                           match uu____11777
                                                           with
                                                           | (vars, guards,
                                                              env'1,
                                                              binder_decls,
                                                              uu____11806) ->
                                                               let uu____11819
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu____11832
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards in
                                                                    (uu____11832,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11836
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1 in
                                                                    (match uu____11836
                                                                    with
                                                                    | 
                                                                    (guard,
                                                                    decls0)
                                                                    ->
                                                                    let uu____11849
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard]) in
                                                                    (uu____11849,
                                                                    decls0)) in
                                                               (match uu____11819
                                                                with
                                                                | (guard,
                                                                   guard_decls)
                                                                    ->
                                                                    let binder_decls1
                                                                    =
                                                                    FStar_List.append
                                                                    binder_decls
                                                                    guard_decls in
                                                                    let decl_g
                                                                    =
                                                                    let uu____11870
                                                                    =
                                                                    let uu____11882
                                                                    =
                                                                    let uu____11885
                                                                    =
                                                                    let uu____11888
                                                                    =
                                                                    let uu____11891
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11891 in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11888 in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11885 in
                                                                    (g,
                                                                    uu____11882,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name")) in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11870 in
                                                                    let env02
                                                                    =
                                                                    FStar_SMTEncoding_Env.push_zfuel_name
                                                                    env01
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                    g in
                                                                    let decl_g_tok
                                                                    =
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications")) in
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let rng =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let app =
                                                                    let uu____11921
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11921 in
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
                                                                    args in
                                                                    let gsapp
                                                                    =
                                                                    let uu____11936
                                                                    =
                                                                    let uu____11939
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm]) in
                                                                    uu____11939
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____11936 in
                                                                    let gmax
                                                                    =
                                                                    let uu____11945
                                                                    =
                                                                    let uu____11948
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    []) in
                                                                    uu____11948
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____11945 in
                                                                    let uu____11953
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1 in
                                                                    (match uu____11953
                                                                    with
                                                                    | 
                                                                    (body_tm,
                                                                    decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11969
                                                                    =
                                                                    let uu____11977
                                                                    =
                                                                    let uu____11978
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____11979
                                                                    =
                                                                    let uu____11995
                                                                    =
                                                                    let uu____11996
                                                                    =
                                                                    let uu____12001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                    (guard,
                                                                    uu____12001) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11996 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11995) in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11978
                                                                    uu____11979 in
                                                                    let uu____12015
                                                                    =
                                                                    let uu____12016
                                                                    =
                                                                    let uu____12018
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu____12018 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12016 in
                                                                    (uu____11977,
                                                                    uu____12015,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11969 in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____12025
                                                                    =
                                                                    let uu____12033
                                                                    =
                                                                    let uu____12034
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____12035
                                                                    =
                                                                    let uu____12046
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12046) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12034
                                                                    uu____12035 in
                                                                    (uu____12033,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12025 in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____12060
                                                                    =
                                                                    let uu____12068
                                                                    =
                                                                    let uu____12069
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____12070
                                                                    =
                                                                    let uu____12081
                                                                    =
                                                                    let uu____12082
                                                                    =
                                                                    let uu____12087
                                                                    =
                                                                    let uu____12088
                                                                    =
                                                                    let uu____12091
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero in
                                                                    uu____12091
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____12088 in
                                                                    (gsapp,
                                                                    uu____12087) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12082 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12081) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12069
                                                                    uu____12070 in
                                                                    (uu____12068,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12060 in
                                                                    let uu____12105
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm) in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____12117
                                                                    =
                                                                    let uu____12118
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12118 in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____12117
                                                                    (fuel ::
                                                                    vars) in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu____12122
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12122 in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____12131
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1 in
                                                                    let uu____12132
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu____12132 in
                                                                    let uu____12134
                                                                    =
                                                                    let uu____12142
                                                                    =
                                                                    let uu____12143
                                                                    =
                                                                    let uu____12148
                                                                    =
                                                                    let uu____12149
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____12150
                                                                    =
                                                                    let uu____12161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12161) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12149
                                                                    uu____12150 in
                                                                    (uu____12148,
                                                                    tot_fun_axioms) in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____12143 in
                                                                    (uu____12142,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12134 in
                                                                    let uu____12174
                                                                    =
                                                                    let uu____12183
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp in
                                                                    match uu____12183
                                                                    with
                                                                    | 
                                                                    (g_typing,
                                                                    d3) ->
                                                                    let uu____12198
                                                                    =
                                                                    let uu____12201
                                                                    =
                                                                    let uu____12202
                                                                    =
                                                                    let uu____12210
                                                                    =
                                                                    let uu____12211
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____12212
                                                                    =
                                                                    let uu____12223
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing) in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12223) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12211
                                                                    uu____12212 in
                                                                    (uu____12210,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12202 in
                                                                    [uu____12201] in
                                                                    (d3,
                                                                    uu____12198) in
                                                                    match uu____12174
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])) in
                                                                    (match uu____12105
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    g_typing)
                                                                    ->
                                                                    let uu____12280
                                                                    =
                                                                    let uu____12283
                                                                    =
                                                                    let uu____12286
                                                                    =
                                                                    let uu____12289
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____12289 in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____12286 in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____12283 in
                                                                    let uu____12296
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    (uu____12280,
                                                                    uu____12296,
                                                                    env02)))))))))) in
                                   let uu____12301 =
                                     let uu____12314 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1 in
                                     FStar_List.fold_left
                                       (fun uu____12377 ->
                                          fun uu____12378 ->
                                            match (uu____12377, uu____12378)
                                            with
                                            | ((decls2, eqns, env01),
                                               (gtok, ty, lb)) ->
                                                let uu____12503 =
                                                  encode_one_binding env01
                                                    gtok ty lb in
                                                (match uu____12503 with
                                                 | (decls', eqns', env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____12314 in
                                   (match uu____12301 with
                                    | (decls2, eqns, env01) ->
                                        let uu____12570 =
                                          let isDeclFun uu___1_12587 =
                                            match uu___1_12587 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12589 -> true
                                            | uu____12602 -> false in
                                          let uu____12604 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten in
                                          FStar_All.pipe_right uu____12604
                                            (fun decls3 ->
                                               let uu____12634 =
                                                 FStar_List.fold_left
                                                   (fun uu____12665 ->
                                                      fun elt ->
                                                        match uu____12665
                                                        with
                                                        | (prefix_decls,
                                                           elts, rest) ->
                                                            let uu____12706 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls) in
                                                            if uu____12706
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12734
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls in
                                                               match uu____12734
                                                               with
                                                               | (elt_decl_funs,
                                                                  elt_rest)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                    elts,
                                                                    (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___873_12772
                                                                    = elt in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___873_12772.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___873_12772.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___873_12772.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3 in
                                               match uu____12634 with
                                               | (prefix_decls, elts, rest)
                                                   ->
                                                   let uu____12804 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial in
                                                   (uu____12804, elts, rest)) in
                                        (match uu____12570 with
                                         | (prefix_decls, elts, rest) ->
                                             let eqns1 = FStar_List.rev eqns in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01))) in
                             let uu____12833 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12839 ->
                                        match uu___2_12839 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                            -> true
                                        | uu____12842 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t ->
                                          let uu____12850 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t) in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12850))) in
                             if uu____12833
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___890_12872 ->
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
                                        Prims.int_one in
                                    let r =
                                      let uu____12917 = FStar_List.hd names in
                                      FStar_All.pipe_right uu____12917
                                        FStar_Pervasives_Native.snd in
                                    ((let uu____12935 =
                                        let uu____12945 =
                                          let uu____12953 =
                                            let uu____12955 =
                                              let uu____12957 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names in
                                              FStar_All.pipe_right
                                                uu____12957
                                                (FStar_String.concat ",") in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12955
                                              (if plural
                                               then "their"
                                               else "its") in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12953, r) in
                                        [uu____12945] in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12935);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable ->
                 let msg =
                   let uu____13016 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13016
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg) in
                 let uu____13035 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial in
                 (uu____13035, env))
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let nm =
        let uu____13091 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13091 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l in
      let uu____13097 = encode_sigelt' env se in
      match uu____13097 with
      | (g, env1) ->
          let g1 =
            match g with
            | [] ->
                ((let uu____13110 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env1.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "SMTEncoding") in
                  if uu____13110
                  then FStar_Util.print1 "Skipped encoding of %s\n" nm
                  else ());
                 (let uu____13118 =
                    let uu____13121 =
                      let uu____13122 = FStar_Util.format1 "<Skipped %s/>" nm in
                      FStar_SMTEncoding_Term.Caption uu____13122 in
                    [uu____13121] in
                  FStar_All.pipe_right uu____13118
                    FStar_SMTEncoding_Term.mk_decls_trivial))
            | uu____13127 ->
                let uu____13128 =
                  let uu____13131 =
                    let uu____13134 =
                      let uu____13135 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____13135 in
                    [uu____13134] in
                  FStar_All.pipe_right uu____13131
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                let uu____13142 =
                  let uu____13145 =
                    let uu____13148 =
                      let uu____13151 =
                        let uu____13152 =
                          FStar_Util.format1 "</end encoding %s>" nm in
                        FStar_SMTEncoding_Term.Caption uu____13152 in
                      [uu____13151] in
                    FStar_All.pipe_right uu____13148
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append g uu____13145 in
                FStar_List.append uu____13128 uu____13142 in
          (g1, env1)
and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      (let uu____13166 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____13166
       then
         let uu____13171 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____13171
       else ());
      (let is_opaque_to_smt t =
         let uu____13183 =
           let uu____13184 = FStar_Syntax_Subst.compress t in
           uu____13184.FStar_Syntax_Syntax.n in
         match uu____13183 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu____13189)) -> s = "opaque_to_smt"
         | uu____13194 -> false in
       let is_uninterpreted_by_smt t =
         let uu____13203 =
           let uu____13204 = FStar_Syntax_Subst.compress t in
           uu____13204.FStar_Syntax_Syntax.n in
         match uu____13203 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu____13209)) -> s = "uninterpreted_by_smt"
         | uu____13214 -> false in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____13220 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu____13232 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____13250 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13251 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____13264 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____13265 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____13276 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____13286 =
             let uu____13288 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname in
             Prims.op_Negation uu____13288 in
           if uu____13286
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____13317 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         ((ed.FStar_Syntax_Syntax.binders), tm,
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))))
                      tm.FStar_Syntax_Syntax.pos in
              let encode_action env1 a =
                let action_defn =
                  let uu____13350 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn in
                  norm_before_encoding env1 uu____13350 in
                let uu____13351 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ in
                match uu____13351 with
                | (formals, uu____13363) ->
                    let arity = FStar_List.length formals in
                    let uu____13371 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity in
                    (match uu____13371 with
                     | (aname, atok, env2) ->
                         let uu____13393 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2 in
                         (match uu____13393 with
                          | (tm, decls) ->
                              let a_decls =
                                let uu____13409 =
                                  let uu____13410 =
                                    let uu____13422 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13442 ->
                                              FStar_SMTEncoding_Term.Term_sort)) in
                                    (aname, uu____13422,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action")) in
                                  FStar_SMTEncoding_Term.DeclFun uu____13410 in
                                [uu____13409;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))] in
                              let uu____13459 =
                                let aux uu____13505 uu____13506 =
                                  match (uu____13505, uu____13506) with
                                  | ((bv, uu____13550),
                                     (env3, acc_sorts, acc)) ->
                                      let uu____13582 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv in
                                      (match uu____13582 with
                                       | (xxsym, xx, env4) ->
                                           let uu____13605 =
                                             let uu____13608 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                             uu____13608 :: acc_sorts in
                                           (env4, uu____13605, (xx :: acc))) in
                                FStar_List.fold_right aux formals
                                  (env2, [], []) in
                              (match uu____13459 with
                               | (uu____13640, xs_sorts, xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                   let a_eq =
                                     let uu____13656 =
                                       let uu____13664 =
                                         let uu____13665 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu____13666 =
                                           let uu____13677 =
                                             let uu____13678 =
                                               let uu____13683 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts in
                                               (app, uu____13683) in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13678 in
                                           ([[app]], xs_sorts, uu____13677) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13665 uu____13666 in
                                       (uu____13664,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality")) in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13656 in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13698 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort) in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13698 in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts in
                                     let uu____13701 =
                                       let uu____13709 =
                                         let uu____13710 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu____13711 =
                                           let uu____13722 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app) in
                                           ([[tok_app]], xs_sorts,
                                             uu____13722) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13710 uu____13711 in
                                       (uu____13709,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence")) in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13701 in
                                   let uu____13735 =
                                     let uu____13738 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial in
                                     FStar_List.append decls uu____13738 in
                                   (env2, uu____13735)))) in
              let uu____13747 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions in
              match uu____13747 with
              | (env1, decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13773, uu____13774)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13775 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4)) in
           (match uu____13775 with | (tname, ttok, env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, us, t) ->
           let uu____13799 = FStar_Syntax_Subst.open_univ_vars us t in
           (match uu____13799 with
            | (us1, t1) ->
                let quals = se.FStar_Syntax_Syntax.sigquals in
                let will_encode_definition =
                  let uu____13815 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some
                         (fun uu___3_13821 ->
                            match uu___3_13821 with
                            | FStar_Syntax_Syntax.Assumption -> true
                            | FStar_Syntax_Syntax.Projector uu____13824 ->
                                true
                            | FStar_Syntax_Syntax.Discriminator uu____13830
                                -> true
                            | FStar_Syntax_Syntax.Irreducible -> true
                            | uu____13833 -> false)) in
                  Prims.op_Negation uu____13815 in
                if will_encode_definition
                then ([], env)
                else
                  (let fv =
                     FStar_Syntax_Syntax.lid_as_fv lid
                       FStar_Syntax_Syntax.delta_constant
                       FStar_Pervasives_Native.None in
                   let uu____13843 =
                     let uu____13848 =
                       FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                         (FStar_Util.for_some is_uninterpreted_by_smt) in
                     encode_top_level_val uu____13848 env fv us1 t1 quals in
                   match uu____13843 with
                   | (decls, env1) ->
                       let tname = FStar_Ident.string_of_lid lid in
                       let tsym =
                         let uu____13862 =
                           FStar_SMTEncoding_Env.try_lookup_free_var env1 lid in
                         FStar_Option.get uu____13862 in
                       let uu____13865 =
                         let uu____13866 =
                           let uu____13869 =
                             primitive_type_axioms
                               env1.FStar_SMTEncoding_Env.tcenv lid tname
                               tsym in
                           FStar_All.pipe_right uu____13869
                             FStar_SMTEncoding_Term.mk_decls_trivial in
                         FStar_List.append decls uu____13866 in
                       (uu____13865, env1)))
       | FStar_Syntax_Syntax.Sig_assume (l, us, f) ->
           let uu____13879 = FStar_Syntax_Subst.open_univ_vars us f in
           (match uu____13879 with
            | (uvs, f1) ->
                let env1 =
                  let uu___1040_13891 = env in
                  let uu____13892 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1040_13891.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1040_13891.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1040_13891.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13892;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1040_13891.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1040_13891.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1040_13891.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1040_13891.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1040_13891.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1040_13891.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1040_13891.FStar_SMTEncoding_Env.global_cache)
                  } in
                let f2 = norm_before_encoding env1 f1 in
                let uu____13894 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1 in
                (match uu____13894 with
                 | (f3, decls) ->
                     let g =
                       let uu____13908 =
                         let uu____13911 =
                           let uu____13912 =
                             let uu____13920 =
                               let uu____13921 =
                                 let uu____13923 =
                                   FStar_Syntax_Print.lid_to_string l in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13923 in
                               FStar_Pervasives_Native.Some uu____13921 in
                             let uu____13927 =
                               let uu____13929 =
                                 let uu____13931 =
                                   FStar_Ident.string_of_lid l in
                                 Prims.op_Hat "assumption_" uu____13931 in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu____13929 in
                             (f3, uu____13920, uu____13927) in
                           FStar_SMTEncoding_Util.mkAssume uu____13912 in
                         [uu____13911] in
                       FStar_All.pipe_right uu____13908
                         FStar_SMTEncoding_Term.mk_decls_trivial in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____13940) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____13954 =
             FStar_Util.fold_map
               (fun env1 ->
                  fun lb ->
                    let lid =
                      let uu____13976 =
                        let uu____13979 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        uu____13979.FStar_Syntax_Syntax.fv_name in
                      uu____13976.FStar_Syntax_Syntax.v in
                    let uu____13980 =
                      let uu____13982 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid in
                      FStar_All.pipe_left FStar_Option.isNone uu____13982 in
                    if uu____13980
                    then
                      let val_decl =
                        let uu___1057_14014 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1057_14014.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1057_14014.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1057_14014.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1057_14014.FStar_Syntax_Syntax.sigopts)
                        } in
                      let uu____14015 = encode_sigelt' env1 val_decl in
                      match uu____14015 with | (decls, env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
           (match uu____13954 with
            | (env1, decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____14051,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
               FStar_Syntax_Syntax.lbunivs = uu____14053;
               FStar_Syntax_Syntax.lbtyp = uu____14054;
               FStar_Syntax_Syntax.lbeff = uu____14055;
               FStar_Syntax_Syntax.lbdef = uu____14056;
               FStar_Syntax_Syntax.lbattrs = uu____14057;
               FStar_Syntax_Syntax.lbpos = uu____14058;_}::[]),
            uu____14059)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu____14078 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one in
           (match uu____14078 with
            | (tname, ttok, env1) ->
                let xx =
                  FStar_SMTEncoding_Term.mk_fv
                    ("x", FStar_SMTEncoding_Term.Term_sort) in
                let x = FStar_SMTEncoding_Util.mkFreeV xx in
                let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                let valid_b2t_x =
                  FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
                let decls =
                  let uu____14116 =
                    let uu____14119 =
                      let uu____14120 =
                        let uu____14128 =
                          let uu____14129 =
                            FStar_Syntax_Syntax.range_of_fv b2t in
                          let uu____14130 =
                            let uu____14141 =
                              let uu____14142 =
                                let uu____14147 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x]) in
                                (valid_b2t_x, uu____14147) in
                              FStar_SMTEncoding_Util.mkEq uu____14142 in
                            ([[b2t_x]], [xx], uu____14141) in
                          FStar_SMTEncoding_Term.mkForall uu____14129
                            uu____14130 in
                        (uu____14128,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def") in
                      FStar_SMTEncoding_Util.mkAssume uu____14120 in
                    [uu____14119] in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____14116 in
                let uu____14185 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                (uu____14185, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____14188, uu____14189) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_14199 ->
                   match uu___4_14199 with
                   | FStar_Syntax_Syntax.Discriminator uu____14201 -> true
                   | uu____14203 -> false))
           ->
           ((let uu____14206 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____14206
             then
               let uu____14211 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding discriminator '%s'\n"
                 uu____14211
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let (uu____14216, lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l ->
                    let uu____14228 =
                      let uu____14230 =
                        let uu____14231 = FStar_Ident.ns_of_lid l in
                        FStar_List.hd uu____14231 in
                      FStar_Ident.string_of_id uu____14230 in
                    uu____14228 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_14240 ->
                      match uu___5_14240 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                          -> true
                      | uu____14243 -> false)))
           ->
           ((let uu____14246 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____14246
             then
               let uu____14251 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding unfold let from Prims '%s'\n"
                 uu____14251
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____14257) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_14271 ->
                   match uu___6_14271 with
                   | FStar_Syntax_Syntax.Projector uu____14273 -> true
                   | uu____14279 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
           let uu____14283 = FStar_SMTEncoding_Env.try_lookup_free_var env l in
           (match uu____14283 with
            | FStar_Pervasives_Native.Some uu____14290 -> ([], env)
            | FStar_Pervasives_Native.None ->
                let se1 =
                  let uu___1126_14292 = se in
                  let uu____14293 = FStar_Ident.range_of_lid l in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____14293;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1126_14292.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1126_14292.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1126_14292.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1126_14292.FStar_Syntax_Syntax.sigopts)
                  } in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____14296) ->
           let uu____14307 =
             FStar_Syntax_Subst.open_let_rec bindings
               FStar_Syntax_Util.exp_unit in
           (match uu____14307 with
            | (bindings1, uu____14319) ->
                let bindings2 =
                  FStar_List.map
                    (fun lb ->
                       let def =
                         norm_before_encoding env
                           lb.FStar_Syntax_Syntax.lbdef in
                       let typ =
                         norm_before_encoding env
                           lb.FStar_Syntax_Syntax.lbtyp in
                       let uu___1141_14334 = lb in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1141_14334.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1141_14334.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = typ;
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1141_14334.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = def;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1141_14334.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1141_14334.FStar_Syntax_Syntax.lbpos)
                       }) bindings1 in
                let uu____14335 =
                  FStar_Syntax_Subst.close_let_rec bindings2
                    FStar_Syntax_Util.exp_unit in
                (match uu____14335 with
                 | (bindings3, uu____14347) ->
                     encode_top_level_let env (is_rec, bindings3)
                       se.FStar_Syntax_Syntax.sigquals))
       | FStar_Syntax_Syntax.Sig_bundle (ses, uu____14356) ->
           let uu____14365 = encode_sigelts env ses in
           (match uu____14365 with
            | (g, env1) ->
                let uu____14376 =
                  FStar_List.fold_left
                    (fun uu____14400 ->
                       fun elt ->
                         match uu____14400 with
                         | (g', inversions) ->
                             let uu____14428 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_14451 ->
                                       match uu___7_14451 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____14453;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____14454;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____14455;_}
                                           -> false
                                       | uu____14462 -> true)) in
                             (match uu____14428 with
                              | (elt_g', elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1170_14487 = elt in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1170_14487.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1170_14487.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1170_14487.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g in
                (match uu____14376 with
                 | (g', inversions) ->
                     let uu____14506 =
                       FStar_List.fold_left
                         (fun uu____14537 ->
                            fun elt ->
                              match uu____14537 with
                              | (decls, elts, rest) ->
                                  let uu____14578 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14587 ->
                                            match uu___8_14587 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14589 -> true
                                            | uu____14602 -> false)
                                         elt.FStar_SMTEncoding_Term.decls) in
                                  if uu____14578
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14625 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14646 ->
                                               match uu___9_14646 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14648 -> true
                                               | uu____14661 -> false)) in
                                     match uu____14625 with
                                     | (elt_decls, elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1192_14692 = elt in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1192_14692.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1192_14692.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1192_14692.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g' in
                     (match uu____14506 with
                      | (decls, elts, rest) ->
                          let uu____14718 =
                            let uu____14719 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial in
                            let uu____14726 =
                              let uu____14729 =
                                let uu____14732 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append rest uu____14732 in
                              FStar_List.append elts uu____14729 in
                            FStar_List.append uu____14719 uu____14726 in
                          (uu____14718, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t, universe_names, tps, k, uu____14743, datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv in
           let uu____14754 =
             FStar_Syntax_Subst.univ_var_opening universe_names in
           (match uu____14754 with
            | (usubst, uvs) ->
                let uu____14777 =
                  let uu____14794 =
                    FStar_TypeChecker_Env.push_univ_vars tcenv uvs in
                  let uu____14795 =
                    FStar_Syntax_Subst.subst_binders usubst tps in
                  let uu____14804 =
                    let uu____14807 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                        usubst in
                    FStar_Syntax_Subst.subst uu____14807 k in
                  (uu____14794, uu____14795, uu____14804) in
                (match uu____14777 with
                 | (tcenv1, tps1, k1) ->
                     let is_injective =
                       let env1 = tcenv1 in
                       let uu____14856 = FStar_Syntax_Subst.open_term tps1 k1 in
                       match uu____14856 with
                       | (tps2, k2) ->
                           let uu____14864 =
                             FStar_Syntax_Util.arrow_formals k2 in
                           (match uu____14864 with
                            | (uu____14872, k3) ->
                                let uu____14878 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2 in
                                (match uu____14878 with
                                 | (tps3, env_tps, uu____14890, us) ->
                                     let u_k =
                                       let uu____14893 =
                                         let uu____14894 =
                                           FStar_Syntax_Syntax.fvar t
                                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                                Prims.int_zero)
                                             FStar_Pervasives_Native.None in
                                         let uu____14896 =
                                           let uu____14897 =
                                             FStar_Syntax_Util.args_of_binders
                                               tps3 in
                                           FStar_Pervasives_Native.snd
                                             uu____14897 in
                                         let uu____14902 =
                                           FStar_Ident.range_of_lid t in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____14894 uu____14896
                                           uu____14902 in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14893 k3 in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero,
                                          uu____14916) -> true
                                       | (FStar_Syntax_Syntax.U_succ u0,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name u0,
                                          FStar_Syntax_Syntax.U_name v0) ->
                                           FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14922,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max us1,
                                          uu____14925) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1 -> universe_leq u1 v))
                                       | (uu____14933,
                                          FStar_Syntax_Syntax.U_max vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown,
                                          uu____14940) ->
                                           let uu____14941 =
                                             let uu____14943 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14943 in
                                           failwith uu____14941
                                       | (uu____14947,
                                          FStar_Syntax_Syntax.U_unknown) ->
                                           let uu____14948 =
                                             let uu____14950 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14950 in
                                           failwith uu____14948
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14954, uu____14955) ->
                                           let uu____14966 =
                                             let uu____14968 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14968 in
                                           failwith uu____14966
                                       | (uu____14972,
                                          FStar_Syntax_Syntax.U_unif
                                          uu____14973) ->
                                           let uu____14984 =
                                             let uu____14986 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14986 in
                                           failwith uu____14984
                                       | uu____14990 -> false in
                                     let u_leq_u_k u =
                                       let uu____15003 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u in
                                       universe_leq uu____15003 u_k in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort in
                                       let uu____15021 = u_leq_u_k u_tp in
                                       if uu____15021
                                       then true
                                       else
                                         (let uu____15028 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp in
                                          match uu____15028 with
                                          | (formals, uu____15037) ->
                                              let uu____15042 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals in
                                              (match uu____15042 with
                                               | (uu____15052, uu____15053,
                                                  uu____15054, u_formals) ->
                                                   FStar_Util.for_all
                                                     (fun u_formal ->
                                                        u_leq_u_k u_formal)
                                                     u_formals)) in
                                     FStar_List.forall2 tp_ok tps3 us)) in
                     ((let uu____15065 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncoding") in
                       if uu____15065
                       then
                         let uu____15070 = FStar_Ident.string_of_lid t in
                         FStar_Util.print2 "%s injectivity for %s\n"
                           (if is_injective then "YES" else "NO") uu____15070
                       else ());
                      (let quals = se.FStar_Syntax_Syntax.sigquals in
                       let is_logical =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___10_15090 ->
                                 match uu___10_15090 with
                                 | FStar_Syntax_Syntax.Logic -> true
                                 | FStar_Syntax_Syntax.Assumption -> true
                                 | uu____15094 -> false)) in
                       let constructor_or_logic_type_decl c =
                         if is_logical
                         then
                           let uu____15107 = c in
                           match uu____15107 with
                           | (name, args, uu____15112, uu____15113,
                              uu____15114) ->
                               let uu____15125 =
                                 let uu____15126 =
                                   let uu____15138 =
                                     FStar_All.pipe_right args
                                       (FStar_List.map
                                          (fun uu____15165 ->
                                             match uu____15165 with
                                             | (uu____15174, sort,
                                                uu____15176) -> sort)) in
                                   (name, uu____15138,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     FStar_Pervasives_Native.None) in
                                 FStar_SMTEncoding_Term.DeclFun uu____15126 in
                               [uu____15125]
                         else
                           (let uu____15187 = FStar_Ident.range_of_lid t in
                            FStar_SMTEncoding_Term.constructor_to_decl
                              uu____15187 c) in
                       let inversion_axioms tapp vars =
                         let uu____15205 =
                           FStar_All.pipe_right datas
                             (FStar_Util.for_some
                                (fun l ->
                                   let uu____15213 =
                                     FStar_TypeChecker_Env.try_lookup_lid
                                       env.FStar_SMTEncoding_Env.tcenv l in
                                   FStar_All.pipe_right uu____15213
                                     FStar_Option.isNone)) in
                         if uu____15205
                         then []
                         else
                           (let uu____15248 =
                              FStar_SMTEncoding_Env.fresh_fvar
                                env.FStar_SMTEncoding_Env.current_module_name
                                "x" FStar_SMTEncoding_Term.Term_sort in
                            match uu____15248 with
                            | (xxsym, xx) ->
                                let uu____15261 =
                                  FStar_All.pipe_right datas
                                    (FStar_List.fold_left
                                       (fun uu____15300 ->
                                          fun l ->
                                            match uu____15300 with
                                            | (out, decls) ->
                                                let uu____15320 =
                                                  FStar_TypeChecker_Env.lookup_datacon
                                                    env.FStar_SMTEncoding_Env.tcenv
                                                    l in
                                                (match uu____15320 with
                                                 | (uu____15331, data_t) ->
                                                     let uu____15333 =
                                                       FStar_Syntax_Util.arrow_formals
                                                         data_t in
                                                     (match uu____15333 with
                                                      | (args, res) ->
                                                          let indices =
                                                            let uu____15353 =
                                                              let uu____15354
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  res in
                                                              uu____15354.FStar_Syntax_Syntax.n in
                                                            match uu____15353
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_app
                                                                (uu____15357,
                                                                 indices)
                                                                -> indices
                                                            | uu____15383 ->
                                                                [] in
                                                          let env1 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.fold_left
                                                                 (fun env1 ->
                                                                    fun
                                                                    uu____15413
                                                                    ->
                                                                    match uu____15413
                                                                    with
                                                                    | 
                                                                    (x,
                                                                    uu____15421)
                                                                    ->
                                                                    let uu____15426
                                                                    =
                                                                    let uu____15427
                                                                    =
                                                                    let uu____15435
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x in
                                                                    (uu____15435,
                                                                    [xx]) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____15427 in
                                                                    FStar_SMTEncoding_Env.push_term_var
                                                                    env1 x
                                                                    uu____15426)
                                                                 env) in
                                                          let uu____15440 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_args
                                                              indices env1 in
                                                          (match uu____15440
                                                           with
                                                           | (indices1,
                                                              decls') ->
                                                               (if
                                                                  (FStar_List.length
                                                                    indices1)
                                                                    <>
                                                                    (
                                                                    FStar_List.length
                                                                    vars)
                                                                then
                                                                  failwith
                                                                    "Impossible"
                                                                else ();
                                                                (let eqs =
                                                                   if
                                                                    is_injective
                                                                   then
                                                                    FStar_List.map2
                                                                    (fun v ->
                                                                    fun a ->
                                                                    let uu____15475
                                                                    =
                                                                    let uu____15480
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    (uu____15480,
                                                                    a) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____15475)
                                                                    vars
                                                                    indices1
                                                                   else [] in
                                                                 let uu____15483
                                                                   =
                                                                   let uu____15484
                                                                    =
                                                                    let uu____15489
                                                                    =
                                                                    let uu____15490
                                                                    =
                                                                    let uu____15495
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_data_tester
                                                                    env1 l xx in
                                                                    let uu____15496
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    eqs
                                                                    FStar_SMTEncoding_Util.mk_and_l in
                                                                    (uu____15495,
                                                                    uu____15496) in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____15490 in
                                                                    (out,
                                                                    uu____15489) in
                                                                   FStar_SMTEncoding_Util.mkOr
                                                                    uu____15484 in
                                                                 (uu____15483,
                                                                   (FStar_List.append
                                                                    decls
                                                                    decls'))))))))
                                       (FStar_SMTEncoding_Util.mkFalse, [])) in
                                (match uu____15261 with
                                 | (data_ax, decls) ->
                                     let uu____15511 =
                                       FStar_SMTEncoding_Env.fresh_fvar
                                         env.FStar_SMTEncoding_Env.current_module_name
                                         "f" FStar_SMTEncoding_Term.Fuel_sort in
                                     (match uu____15511 with
                                      | (ffsym, ff) ->
                                          let fuel_guarded_inversion =
                                            let xx_has_type_sfuel =
                                              if
                                                (FStar_List.length datas) >
                                                  Prims.int_one
                                              then
                                                let uu____15528 =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    ("SFuel", [ff]) in
                                                FStar_SMTEncoding_Term.mk_HasTypeFuel
                                                  uu____15528 xx tapp
                                              else
                                                FStar_SMTEncoding_Term.mk_HasTypeFuel
                                                  ff xx tapp in
                                            let uu____15535 =
                                              let uu____15543 =
                                                let uu____15544 =
                                                  FStar_Ident.range_of_lid t in
                                                let uu____15545 =
                                                  let uu____15556 =
                                                    let uu____15557 =
                                                      FStar_SMTEncoding_Term.mk_fv
                                                        (ffsym,
                                                          FStar_SMTEncoding_Term.Fuel_sort) in
                                                    let uu____15559 =
                                                      let uu____15562 =
                                                        FStar_SMTEncoding_Term.mk_fv
                                                          (xxsym,
                                                            FStar_SMTEncoding_Term.Term_sort) in
                                                      uu____15562 :: vars in
                                                    FStar_SMTEncoding_Env.add_fuel
                                                      uu____15557 uu____15559 in
                                                  let uu____15564 =
                                                    FStar_SMTEncoding_Util.mkImp
                                                      (xx_has_type_sfuel,
                                                        data_ax) in
                                                  ([[xx_has_type_sfuel]],
                                                    uu____15556, uu____15564) in
                                                FStar_SMTEncoding_Term.mkForall
                                                  uu____15544 uu____15545 in
                                              let uu____15573 =
                                                let uu____15575 =
                                                  let uu____15577 =
                                                    FStar_Ident.string_of_lid
                                                      t in
                                                  Prims.op_Hat
                                                    "fuel_guarded_inversion_"
                                                    uu____15577 in
                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                  uu____15575 in
                                              (uu____15543,
                                                (FStar_Pervasives_Native.Some
                                                   "inversion axiom"),
                                                uu____15573) in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15535 in
                                          let uu____15583 =
                                            FStar_All.pipe_right
                                              [fuel_guarded_inversion]
                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                          FStar_List.append decls uu____15583))) in
                       let uu____15590 =
                         let k2 =
                           match tps1 with
                           | [] -> k1
                           | uu____15604 ->
                               let uu____15613 =
                                 let uu____15614 =
                                   let uu____15629 =
                                     FStar_Syntax_Syntax.mk_Total k1 in
                                   (tps1, uu____15629) in
                                 FStar_Syntax_Syntax.Tm_arrow uu____15614 in
                               FStar_Syntax_Syntax.mk uu____15613
                                 k1.FStar_Syntax_Syntax.pos in
                         let k3 = norm_before_encoding env k2 in
                         FStar_Syntax_Util.arrow_formals k3 in
                       match uu____15590 with
                       | (formals, res) ->
                           let uu____15653 =
                             FStar_SMTEncoding_EncodeTerm.encode_binders
                               FStar_Pervasives_Native.None formals env in
                           (match uu____15653 with
                            | (vars, guards, env', binder_decls, uu____15678)
                                ->
                                let arity = FStar_List.length vars in
                                let uu____15692 =
                                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                                    env t arity in
                                (match uu____15692 with
                                 | (tname, ttok, env1) ->
                                     let ttok_tm =
                                       FStar_SMTEncoding_Util.mkApp
                                         (ttok, []) in
                                     let guard =
                                       FStar_SMTEncoding_Util.mk_and_l guards in
                                     let tapp =
                                       let uu____15718 =
                                         let uu____15726 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (tname, uu____15726) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____15718 in
                                     let uu____15732 =
                                       let tname_decl =
                                         let uu____15742 =
                                           let uu____15743 =
                                             FStar_All.pipe_right vars
                                               (FStar_List.map
                                                  (fun fv ->
                                                     let uu____15762 =
                                                       let uu____15764 =
                                                         FStar_SMTEncoding_Term.fv_name
                                                           fv in
                                                       Prims.op_Hat tname
                                                         uu____15764 in
                                                     let uu____15766 =
                                                       FStar_SMTEncoding_Term.fv_sort
                                                         fv in
                                                     (uu____15762,
                                                       uu____15766, false))) in
                                           let uu____15770 =
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                               () in
                                           (tname, uu____15743,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             uu____15770, false) in
                                         constructor_or_logic_type_decl
                                           uu____15742 in
                                       let uu____15778 =
                                         match vars with
                                         | [] ->
                                             let uu____15791 =
                                               let uu____15792 =
                                                 let uu____15795 =
                                                   FStar_SMTEncoding_Util.mkApp
                                                     (tname, []) in
                                                 FStar_All.pipe_left
                                                   (fun uu____15801 ->
                                                      FStar_Pervasives_Native.Some
                                                        uu____15801)
                                                   uu____15795 in
                                               FStar_SMTEncoding_Env.push_free_var
                                                 env1 t arity tname
                                                 uu____15792 in
                                             ([], uu____15791)
                                         | uu____15804 ->
                                             let ttok_decl =
                                               FStar_SMTEncoding_Term.DeclFun
                                                 (ttok, [],
                                                   FStar_SMTEncoding_Term.Term_sort,
                                                   (FStar_Pervasives_Native.Some
                                                      "token")) in
                                             let ttok_fresh =
                                               let uu____15814 =
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                   () in
                                               FStar_SMTEncoding_Term.fresh_token
                                                 (ttok_tm, [],
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                 uu____15814 in
                                             let ttok_app =
                                               FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                 ttok_tm vars in
                                             let pats = [[ttok_app]; [tapp]] in
                                             let name_tok_corr =
                                               let uu____15837 =
                                                 let uu____15845 =
                                                   let uu____15846 =
                                                     FStar_Ident.range_of_lid
                                                       t in
                                                   let uu____15847 =
                                                     let uu____15863 =
                                                       FStar_SMTEncoding_Util.mkEq
                                                         (ttok_app, tapp) in
                                                     (pats,
                                                       FStar_Pervasives_Native.None,
                                                       vars, uu____15863) in
                                                   FStar_SMTEncoding_Term.mkForall'
                                                     uu____15846 uu____15847 in
                                                 (uu____15845,
                                                   (FStar_Pervasives_Native.Some
                                                      "name-token correspondence"),
                                                   (Prims.op_Hat
                                                      "token_correspondence_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15837 in
                                             ([ttok_decl;
                                              ttok_fresh;
                                              name_tok_corr], env1) in
                                       match uu____15778 with
                                       | (tok_decls, env2) ->
                                           let uu____15890 =
                                             FStar_Ident.lid_equals t
                                               FStar_Parser_Const.lex_t_lid in
                                           if uu____15890
                                           then (tok_decls, env2)
                                           else
                                             ((FStar_List.append tname_decl
                                                 tok_decls), env2) in
                                     (match uu____15732 with
                                      | (decls, env2) ->
                                          let kindingAx =
                                            let uu____15918 =
                                              FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                FStar_Pervasives_Native.None
                                                res env' tapp in
                                            match uu____15918 with
                                            | (k2, decls1) ->
                                                let karr =
                                                  if
                                                    (FStar_List.length
                                                       formals)
                                                      > Prims.int_zero
                                                  then
                                                    let uu____15940 =
                                                      let uu____15941 =
                                                        let uu____15949 =
                                                          let uu____15950 =
                                                            FStar_SMTEncoding_Term.mk_PreType
                                                              ttok_tm in
                                                          FStar_SMTEncoding_Term.mk_tester
                                                            "Tm_arrow"
                                                            uu____15950 in
                                                        (uu____15949,
                                                          (FStar_Pervasives_Native.Some
                                                             "kinding"),
                                                          (Prims.op_Hat
                                                             "pre_kinding_"
                                                             ttok)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____15941 in
                                                    [uu____15940]
                                                  else [] in
                                                let rng =
                                                  FStar_Ident.range_of_lid t in
                                                let tot_fun_axioms =
                                                  let uu____15960 =
                                                    FStar_List.map
                                                      (fun uu____15964 ->
                                                         FStar_SMTEncoding_Util.mkTrue)
                                                      vars in
                                                  FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                    rng ttok_tm vars
                                                    uu____15960 true in
                                                let uu____15966 =
                                                  let uu____15969 =
                                                    let uu____15972 =
                                                      let uu____15975 =
                                                        let uu____15976 =
                                                          let uu____15984 =
                                                            let uu____15985 =
                                                              let uu____15990
                                                                =
                                                                let uu____15991
                                                                  =
                                                                  let uu____16002
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    k2) in
                                                                  ([[tapp]],
                                                                    vars,
                                                                    uu____16002) in
                                                                FStar_SMTEncoding_Term.mkForall
                                                                  rng
                                                                  uu____15991 in
                                                              (tot_fun_axioms,
                                                                uu____15990) in
                                                            FStar_SMTEncoding_Util.mkAnd
                                                              uu____15985 in
                                                          (uu____15984,
                                                            FStar_Pervasives_Native.None,
                                                            (Prims.op_Hat
                                                               "kinding_"
                                                               ttok)) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____15976 in
                                                      [uu____15975] in
                                                    FStar_List.append karr
                                                      uu____15972 in
                                                  FStar_All.pipe_right
                                                    uu____15969
                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                FStar_List.append decls1
                                                  uu____15966 in
                                          let aux =
                                            let uu____16021 =
                                              let uu____16024 =
                                                inversion_axioms tapp vars in
                                              let uu____16027 =
                                                let uu____16030 =
                                                  let uu____16033 =
                                                    let uu____16034 =
                                                      FStar_Ident.range_of_lid
                                                        t in
                                                    pretype_axiom uu____16034
                                                      env2 tapp vars in
                                                  [uu____16033] in
                                                FStar_All.pipe_right
                                                  uu____16030
                                                  FStar_SMTEncoding_Term.mk_decls_trivial in
                                              FStar_List.append uu____16024
                                                uu____16027 in
                                            FStar_List.append kindingAx
                                              uu____16021 in
                                          let g =
                                            let uu____16042 =
                                              FStar_All.pipe_right decls
                                                FStar_SMTEncoding_Term.mk_decls_trivial in
                                            FStar_List.append uu____16042
                                              (FStar_List.append binder_decls
                                                 aux) in
                                          (g, env2))))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d, uu____16050, uu____16051, uu____16052, uu____16053,
            uu____16054)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d, us, t, uu____16064, n_tps, uu____16066) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____16076 = FStar_Syntax_Subst.open_univ_vars us t in
           (match uu____16076 with
            | (us1, t1) ->
                let uu____16087 =
                  let uu____16096 =
                    FStar_List.map
                      FStar_SMTEncoding_EncodeTerm.encode_univ_name us1 in
                  FStar_All.pipe_right uu____16096 FStar_List.unzip in
                (match uu____16087 with
                 | (univ_fvs, univs) ->
                     let univ_sorts =
                       FStar_All.pipe_right univs
                         (FStar_List.map
                            (fun uu____16143 ->
                               FStar_SMTEncoding_Term.univ_sort)) in
                     let t2 = norm_before_encoding env t1 in
                     let uu____16145 = FStar_Syntax_Util.arrow_formals t2 in
                     (match uu____16145 with
                      | (formals, t_res) ->
                          let arity = FStar_List.length formals in
                          let uu____16169 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env d arity in
                          (match uu____16169 with
                           | (ddconstrsym, ddtok, env1) ->
                               let ddtok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ddtok, univs) in
                               let uu____16193 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env1.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____16193 with
                                | (fuel_var, fuel_tm) ->
                                    let s_fuel_tm =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [fuel_tm]) in
                                    let uu____16213 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1 in
                                    (match uu____16213 with
                                     | (vars, guards, env', binder_decls,
                                        names) ->
                                         let univ_fields =
                                           FStar_All.pipe_right univs
                                             (FStar_List.mapi
                                                (fun i ->
                                                   fun uu____16271 ->
                                                     let bv =
                                                       let uu___1453_16274 =
                                                         FStar_Syntax_Syntax.null_bv
                                                           FStar_Syntax_Syntax.tun in
                                                       let uu____16275 =
                                                         FStar_Ident.mk_ident
                                                           ((Prims.string_of_int
                                                               i),
                                                             FStar_Range.dummyRange) in
                                                       {
                                                         FStar_Syntax_Syntax.ppname
                                                           = uu____16275;
                                                         FStar_Syntax_Syntax.index
                                                           =
                                                           (uu___1453_16274.FStar_Syntax_Syntax.index);
                                                         FStar_Syntax_Syntax.sort
                                                           =
                                                           (uu___1453_16274.FStar_Syntax_Syntax.sort)
                                                       } in
                                                     let uu____16277 =
                                                       FStar_SMTEncoding_Env.mk_term_projector_name
                                                         d bv in
                                                     (uu____16277,
                                                       FStar_SMTEncoding_Term.univ_sort,
                                                       true))) in
                                         let n_univs =
                                           FStar_List.length univ_fields in
                                         let fields =
                                           FStar_All.pipe_right names
                                             (FStar_List.mapi
                                                (fun _i ->
                                                   fun x ->
                                                     let projectible = true in
                                                     let uu____16308 =
                                                       FStar_SMTEncoding_Env.mk_term_projector_name
                                                         d x in
                                                     (uu____16308,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       projectible))) in
                                         let datacons =
                                           let uu____16315 =
                                             let uu____16316 =
                                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                 () in
                                             (ddconstrsym,
                                               (FStar_List.append univ_fields
                                                  fields),
                                               FStar_SMTEncoding_Term.Term_sort,
                                               uu____16316, true) in
                                           let uu____16324 =
                                             let uu____16331 =
                                               FStar_Ident.range_of_lid d in
                                             FStar_SMTEncoding_Term.constructor_to_decl
                                               uu____16331 in
                                           FStar_All.pipe_right uu____16315
                                             uu____16324 in
                                         let app =
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             ddtok_tm vars in
                                         let guard =
                                           FStar_SMTEncoding_Util.mk_and_l
                                             guards in
                                         let xvars =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         let dapp =
                                           FStar_SMTEncoding_Util.mkApp
                                             (ddconstrsym,
                                               (FStar_List.append univs xvars)) in
                                         let uu____16343 =
                                           FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                             FStar_Pervasives_Native.None t2
                                             env1 ddtok_tm in
                                         (match uu____16343 with
                                          | (tok_typing, decls3) ->
                                              let tok_typing1 =
                                                match (fields, univs) with
                                                | (uu____16359::uu____16360,
                                                   []) ->
                                                    let ff =
                                                      FStar_SMTEncoding_Term.mk_fv
                                                        ("ty",
                                                          FStar_SMTEncoding_Term.Term_sort) in
                                                    let f =
                                                      FStar_SMTEncoding_Util.mkFreeV
                                                        ff in
                                                    let vtok_app_l =
                                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                        ddtok_tm [ff] in
                                                    let vtok_app_r =
                                                      let uu____16389 =
                                                        let uu____16390 =
                                                          FStar_SMTEncoding_Term.mk_fv
                                                            (ddtok,
                                                              FStar_SMTEncoding_Term.Term_sort) in
                                                        [uu____16390] in
                                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                        f uu____16389 in
                                                    let uu____16416 =
                                                      FStar_Ident.range_of_lid
                                                        d in
                                                    let uu____16417 =
                                                      let uu____16428 =
                                                        FStar_SMTEncoding_Term.mk_NoHoist
                                                          f tok_typing in
                                                      ([[vtok_app_l];
                                                       [vtok_app_r]], 
                                                        [ff], uu____16428) in
                                                    FStar_SMTEncoding_Term.mkForall
                                                      uu____16416 uu____16417
                                                | uu____16455 ->
                                                    let uu____16464 =
                                                      FStar_Ident.range_of_lid
                                                        d in
                                                    close_universes
                                                      uu____16464 univ_fvs
                                                      ddtok_tm tok_typing in
                                              let uu____16465 =
                                                FStar_SMTEncoding_EncodeTerm.encode_binders
                                                  (FStar_Pervasives_Native.Some
                                                     fuel_tm) formals env1 in
                                              (match uu____16465 with
                                               | (vars', guards', env'',
                                                  decls_formals, uu____16490)
                                                   ->
                                                   let uu____16503 =
                                                     let xvars1 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars' in
                                                     let dapp1 =
                                                       FStar_SMTEncoding_Util.mkApp
                                                         (ddconstrsym,
                                                           (FStar_List.append
                                                              univs xvars1)) in
                                                     let uu____16521 =
                                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                         (FStar_Pervasives_Native.Some
                                                            fuel_tm) t_res
                                                         env'' dapp1 in
                                                     ((FStar_List.append
                                                         univ_fvs vars'),
                                                       uu____16521) in
                                                   (match uu____16503 with
                                                    | (vars'1,
                                                       (ty_pred', decls_pred))
                                                        ->
                                                        let guard' =
                                                          FStar_SMTEncoding_Util.mk_and_l
                                                            guards' in
                                                        let proxy_fresh =
                                                          match formals with
                                                          | [] -> []
                                                          | uu____16559 ->
                                                              let uu____16560
                                                                =
                                                                let uu____16561
                                                                  =
                                                                  FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                    () in
                                                                FStar_SMTEncoding_Term.fresh_token
                                                                  (ddtok_tm,
                                                                    univ_fvs,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                  uu____16561 in
                                                              [uu____16560] in
                                                        let encode_elim
                                                          uu____16576 =
                                                          let uu____16577 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t_res in
                                                          match uu____16577
                                                          with
                                                          | (head, args) ->
                                                              let uu____16628
                                                                =
                                                                let uu____16629
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    head in
                                                                uu____16629.FStar_Syntax_Syntax.n in
                                                              (match uu____16628
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_uinst
                                                                   ({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_fvar
                                                                    fv;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____16641;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____16642;_},
                                                                    uu____16643)
                                                                   ->
                                                                   let encoded_head_fvb
                                                                    =
                                                                    FStar_SMTEncoding_Env.lookup_free_var_name
                                                                    env'
                                                                    fv.FStar_Syntax_Syntax.fv_name in
                                                                   let uu____16649
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_args
                                                                    args env' in
                                                                   (match uu____16649
                                                                    with
                                                                    | 
                                                                    (encoded_args,
                                                                    arg_decls)
                                                                    ->
                                                                    let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____16712
                                                                    ->
                                                                    let uu____16713
                                                                    =
                                                                    let uu____16719
                                                                    =
                                                                    let uu____16721
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16721 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16719) in
                                                                    FStar_Errors.raise_error
                                                                    uu____16713
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____16744
                                                                    =
                                                                    let uu____16746
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16746 in
                                                                    if
                                                                    uu____16744
                                                                    then
                                                                    let uu____16768
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16768]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                    let uu____16771
                                                                    =
                                                                    let uu____16785
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____16842
                                                                    ->
                                                                    fun
                                                                    uu____16843
                                                                    ->
                                                                    match 
                                                                    (uu____16842,
                                                                    uu____16843)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____16954
                                                                    =
                                                                    let uu____16962
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16962 in
                                                                    (match uu____16954
                                                                    with
                                                                    | 
                                                                    (uu____16976,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16987
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16987
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16992
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                    (env',
                                                                    [], [],
                                                                    Prims.int_zero)
                                                                    uu____16785 in
                                                                    (match uu____16771
                                                                    with
                                                                    | 
                                                                    (uu____17013,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____17016)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    (FStar_List.append
                                                                    univs
                                                                    xvars1)) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____17043
                                                                    =
                                                                    let uu____17051
                                                                    =
                                                                    let uu____17052
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17053
                                                                    =
                                                                    let uu____17064
                                                                    =
                                                                    let uu____17065
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17065
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu____17067
                                                                    =
                                                                    let uu____17068
                                                                    =
                                                                    let uu____17073
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____17073) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17068 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17064,
                                                                    uu____17067) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17052
                                                                    uu____17053 in
                                                                    (uu____17051,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17043 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____17088
                                                                    =
                                                                    let uu____17089
                                                                    =
                                                                    let uu____17095
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu____17095,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17089 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17088 in
                                                                    let prec
                                                                    =
                                                                    let uu____17101
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____17124
                                                                    =
                                                                    let uu____17125
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____17125
                                                                    dapp1 in
                                                                    [uu____17124]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____17101
                                                                    FStar_List.flatten in
                                                                    let uu____17132
                                                                    =
                                                                    let uu____17140
                                                                    =
                                                                    let uu____17141
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17142
                                                                    =
                                                                    let uu____17153
                                                                    =
                                                                    let uu____17154
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17154
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu____17156
                                                                    =
                                                                    let uu____17157
                                                                    =
                                                                    let uu____17162
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____17162) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17157 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17153,
                                                                    uu____17156) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17141
                                                                    uu____17142 in
                                                                    (uu____17140,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17132 in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                               | FStar_Syntax_Syntax.Tm_fvar
                                                                   fv ->
                                                                   let encoded_head_fvb
                                                                    =
                                                                    FStar_SMTEncoding_Env.lookup_free_var_name
                                                                    env'
                                                                    fv.FStar_Syntax_Syntax.fv_name in
                                                                   let uu____17181
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_args
                                                                    args env' in
                                                                   (match uu____17181
                                                                    with
                                                                    | 
                                                                    (encoded_args,
                                                                    arg_decls)
                                                                    ->
                                                                    let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____17244
                                                                    ->
                                                                    let uu____17245
                                                                    =
                                                                    let uu____17251
                                                                    =
                                                                    let uu____17253
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____17253 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____17251) in
                                                                    FStar_Errors.raise_error
                                                                    uu____17245
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____17276
                                                                    =
                                                                    let uu____17278
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____17278 in
                                                                    if
                                                                    uu____17276
                                                                    then
                                                                    let uu____17300
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____17300]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                    let uu____17303
                                                                    =
                                                                    let uu____17317
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____17374
                                                                    ->
                                                                    fun
                                                                    uu____17375
                                                                    ->
                                                                    match 
                                                                    (uu____17374,
                                                                    uu____17375)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____17486
                                                                    =
                                                                    let uu____17494
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____17494 in
                                                                    (match uu____17486
                                                                    with
                                                                    | 
                                                                    (uu____17508,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____17519
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____17519
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____17524
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____17524
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                    (env',
                                                                    [], [],
                                                                    Prims.int_zero)
                                                                    uu____17317 in
                                                                    (match uu____17303
                                                                    with
                                                                    | 
                                                                    (uu____17545,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____17548)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    (FStar_List.append
                                                                    univs
                                                                    xvars1)) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____17575
                                                                    =
                                                                    let uu____17583
                                                                    =
                                                                    let uu____17584
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17585
                                                                    =
                                                                    let uu____17596
                                                                    =
                                                                    let uu____17597
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17597
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu____17599
                                                                    =
                                                                    let uu____17600
                                                                    =
                                                                    let uu____17605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____17605) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17600 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17596,
                                                                    uu____17599) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17584
                                                                    uu____17585 in
                                                                    (uu____17583,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17575 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____17620
                                                                    =
                                                                    let uu____17621
                                                                    =
                                                                    let uu____17627
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu____17627,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17621 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17620 in
                                                                    let prec
                                                                    =
                                                                    let uu____17633
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____17656
                                                                    =
                                                                    let uu____17657
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____17657
                                                                    dapp1 in
                                                                    [uu____17656]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____17633
                                                                    FStar_List.flatten in
                                                                    let uu____17664
                                                                    =
                                                                    let uu____17672
                                                                    =
                                                                    let uu____17673
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17674
                                                                    =
                                                                    let uu____17685
                                                                    =
                                                                    let uu____17686
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17686
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu____17688
                                                                    =
                                                                    let uu____17689
                                                                    =
                                                                    let uu____17694
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____17694) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17689 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17685,
                                                                    uu____17688) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17673
                                                                    uu____17674 in
                                                                    (uu____17672,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17664 in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                               | uu____17711
                                                                   ->
                                                                   ((
                                                                    let uu____17713
                                                                    =
                                                                    let uu____17719
                                                                    =
                                                                    let uu____17721
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    let uu____17723
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    head in
                                                                    FStar_Util.format2
                                                                    "Constructor %s builds an unexpected type %s\n"
                                                                    uu____17721
                                                                    uu____17723 in
                                                                    (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                                    uu____17719) in
                                                                    FStar_Errors.log_issue
                                                                    se.FStar_Syntax_Syntax.sigrng
                                                                    uu____17713);
                                                                    ([], []))) in
                                                        let uu____17731 =
                                                          encode_elim () in
                                                        (match uu____17731
                                                         with
                                                         | (decls2, elim) ->
                                                             let g =
                                                               let uu____17757
                                                                 =
                                                                 let uu____17760
                                                                   =
                                                                   let uu____17763
                                                                    =
                                                                    let uu____17766
                                                                    =
                                                                    let uu____17769
                                                                    =
                                                                    let uu____17772
                                                                    =
                                                                    let uu____17775
                                                                    =
                                                                    let uu____17776
                                                                    =
                                                                    let uu____17788
                                                                    =
                                                                    let uu____17789
                                                                    =
                                                                    let uu____17791
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17791 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17789 in
                                                                    (ddtok,
                                                                    univ_sorts,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17788) in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17776 in
                                                                    [uu____17775] in
                                                                    FStar_List.append
                                                                    uu____17772
                                                                    proxy_fresh in
                                                                    FStar_All.pipe_right
                                                                    uu____17769
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    let uu____17802
                                                                    =
                                                                    let uu____17805
                                                                    =
                                                                    let uu____17808
                                                                    =
                                                                    let uu____17811
                                                                    =
                                                                    let uu____17814
                                                                    =
                                                                    let uu____17817
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok)) in
                                                                    let uu____17822
                                                                    =
                                                                    let uu____17825
                                                                    =
                                                                    let uu____17826
                                                                    =
                                                                    let uu____17834
                                                                    =
                                                                    let uu____17835
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17836
                                                                    =
                                                                    let uu____17847
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    (FStar_List.append
                                                                    univ_fvs
                                                                    vars),
                                                                    uu____17847) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17835
                                                                    uu____17836 in
                                                                    (uu____17834,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17826 in
                                                                    let uu____17860
                                                                    =
                                                                    let uu____17863
                                                                    =
                                                                    let uu____17864
                                                                    =
                                                                    let uu____17872
                                                                    =
                                                                    let uu____17873
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____17874
                                                                    =
                                                                    let uu____17885
                                                                    =
                                                                    let uu____17886
                                                                    =
                                                                    let uu____17889
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17889
                                                                    univ_fvs in
                                                                    FStar_List.append
                                                                    uu____17886
                                                                    vars'1 in
                                                                    let uu____17891
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17885,
                                                                    uu____17891) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17873
                                                                    uu____17874 in
                                                                    (uu____17872,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17864 in
                                                                    [uu____17863] in
                                                                    uu____17825
                                                                    ::
                                                                    uu____17860 in
                                                                    uu____17817
                                                                    ::
                                                                    uu____17822 in
                                                                    FStar_List.append
                                                                    uu____17814
                                                                    elim in
                                                                    FStar_All.pipe_right
                                                                    uu____17811
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    FStar_List.append
                                                                    decls_pred
                                                                    uu____17808 in
                                                                    FStar_List.append
                                                                    decls_formals
                                                                    uu____17805 in
                                                                    FStar_List.append
                                                                    uu____17766
                                                                    uu____17802 in
                                                                   FStar_List.append
                                                                    decls3
                                                                    uu____17763 in
                                                                 FStar_List.append
                                                                   decls2
                                                                   uu____17760 in
                                                               FStar_List.append
                                                                 binder_decls
                                                                 uu____17757 in
                                                             let uu____17908
                                                               =
                                                               let uu____17909
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   datacons
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial in
                                                               FStar_List.append
                                                                 uu____17909
                                                                 g in
                                                             (uu____17908,
                                                               env1))))))))))))
and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun ses ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17943 ->
              fun se ->
                match uu____17943 with
                | (g, env1) ->
                    let uu____17963 = encode_sigelt env1 se in
                    (match uu____17963 with
                     | (g', env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      let encode_binding b uu____18031 =
        match uu____18031 with
        | (i, decls, env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____18068 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort in
                 ((let uu____18076 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____18076
                   then
                     let uu____18081 = FStar_Syntax_Print.bv_to_string x in
                     let uu____18083 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____18085 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____18081 uu____18083 uu____18085
                   else ());
                  (let uu____18090 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1 in
                   match uu____18090 with
                   | (t, decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____18108 =
                         let uu____18116 =
                           let uu____18118 =
                             let uu____18120 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.op_Hat uu____18120
                               (Prims.op_Hat "_" (Prims.string_of_int i)) in
                           Prims.op_Hat "x_" uu____18118 in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____18116 in
                       (match uu____18108 with
                        | (xxsym, xx, env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____18140 = FStar_Options.log_queries () in
                              if uu____18140
                              then
                                let uu____18143 =
                                  let uu____18145 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____18147 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____18149 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____18145 uu____18147 uu____18149 in
                                FStar_Pervasives_Native.Some uu____18143
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              let uu____18165 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial in
                              let uu____18175 =
                                let uu____18178 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append decls' uu____18178 in
                              FStar_List.append uu____18165 uu____18175 in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x, (us, t)) ->
                 let uu____18208 = FStar_Syntax_Subst.open_univ_vars us t in
                 (match uu____18208 with
                  | (us1, t1) ->
                      let t_norm = norm_before_encoding env1 t1 in
                      let fv =
                        FStar_Syntax_Syntax.lid_as_fv x
                          FStar_Syntax_Syntax.delta_constant
                          FStar_Pervasives_Native.None in
                      let uu____18226 =
                        encode_free_var false env1 fv us1 t1 t_norm [] in
                      (match uu____18226 with
                       | (g, env') ->
                           ((i + Prims.int_one), (FStar_List.append decls g),
                             env')))) in
      let uu____18247 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env) in
      match uu____18247 with | (uu____18274, decls, env1) -> (decls, env1)
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____18327 ->
              match uu____18327 with
              | (l, uu____18336, uu____18337) ->
                  let uu____18340 =
                    let uu____18352 = FStar_SMTEncoding_Term.fv_name l in
                    (uu____18352, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None) in
                  FStar_SMTEncoding_Term.DeclFun uu____18340)) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____18385 ->
              match uu____18385 with
              | (l, uu____18396, uu____18397) ->
                  let uu____18400 =
                    let uu____18401 = FStar_SMTEncoding_Term.fv_name l in
                    FStar_All.pipe_left
                      (fun uu____18404 ->
                         FStar_SMTEncoding_Term.Echo uu____18404) uu____18401 in
                  let uu____18405 =
                    let uu____18408 =
                      let uu____18409 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____18409 in
                    [uu____18408] in
                  uu____18400 :: uu____18405)) in
    (prefix, suffix)
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    let uu____18427 =
      let uu____18430 =
        let uu____18431 = FStar_Util.psmap_empty () in
        let uu____18446 =
          let uu____18455 = FStar_Util.psmap_empty () in (uu____18455, []) in
        let uu____18462 =
          let uu____18464 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____18464 FStar_Ident.string_of_lid in
        let uu____18466 = FStar_Util.smap_create (Prims.of_int (100)) in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____18431;
          FStar_SMTEncoding_Env.fvar_bindings = uu____18446;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____18462;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____18466
        } in
      [uu____18430] in
    FStar_ST.op_Colon_Equals last_env uu____18427
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn ->
    fun tcenv ->
      let uu____18510 = FStar_ST.op_Bang last_env in
      match uu____18510 with
      | [] -> failwith "No env; call init first!"
      | e::uu____18538 ->
          let uu___1639_18541 = e in
          let uu____18542 = FStar_Ident.string_of_lid cmn in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1639_18541.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1639_18541.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1639_18541.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1639_18541.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1639_18541.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1639_18541.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1639_18541.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____18542;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1639_18541.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1639_18541.FStar_SMTEncoding_Env.global_cache)
          }
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env ->
    let uu____18550 = FStar_ST.op_Bang last_env in
    match uu____18550 with
    | [] -> failwith "Empty env stack"
    | uu____18577::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
let (push_env : unit -> unit) =
  fun uu____18609 ->
    let uu____18610 = FStar_ST.op_Bang last_env in
    match uu____18610 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
let (pop_env : unit -> unit) =
  fun uu____18670 ->
    let uu____18671 = FStar_ST.op_Bang last_env in
    match uu____18671 with
    | [] -> failwith "Popping an empty stack"
    | uu____18698::tl -> FStar_ST.op_Colon_Equals last_env tl
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18735 -> FStar_Common.snapshot push_env last_env ()
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_env last_env depth
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let (snapshot :
  Prims.string -> (FStar_TypeChecker_Env.solver_depth_t * unit)) =
  fun msg ->
    FStar_Util.atomically
      (fun uu____18788 ->
         let uu____18789 = snapshot_env () in
         match uu____18789 with
         | (env_depth, ()) ->
             let uu____18811 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot () in
             (match uu____18811 with
              | (varops_depth, ()) ->
                  let uu____18833 = FStar_SMTEncoding_Z3.snapshot msg in
                  (match uu____18833 with
                   | (z3_depth, ()) ->
                       ((env_depth, varops_depth, z3_depth), ()))))
let (rollback :
  Prims.string ->
    FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg ->
    fun depth ->
      FStar_Util.atomically
        (fun uu____18891 ->
           let uu____18892 =
             match depth with
             | FStar_Pervasives_Native.Some (s1, s2, s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None) in
           match uu____18892 with
           | (env_depth, varops_depth, z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
let (push : Prims.string -> unit) =
  fun msg -> let uu____18987 = snapshot msg in ()
let (pop : Prims.string -> unit) =
  fun msg -> rollback msg FStar_Pervasives_Native.None
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env -> []
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun fact_db_ids ->
      fun d ->
        match (fact_db_ids, d) with
        | (uu____19033::uu____19034, FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1700_19042 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1700_19042.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1700_19042.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1700_19042.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____19043 -> d
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env ->
    fun fact_db_ids ->
      fun elt ->
        let uu___1706_19070 = elt in
        let uu____19071 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids)) in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1706_19070.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1706_19070.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____19071;
          FStar_SMTEncoding_Term.a_names =
            (uu___1706_19070.FStar_SMTEncoding_Term.a_names)
        }
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env ->
    fun lid ->
      let uu____19091 =
        let uu____19094 =
          let uu____19095 =
            let uu____19096 = FStar_Ident.ns_of_lid lid in
            FStar_Ident.lid_of_ids uu____19096 in
          FStar_SMTEncoding_Term.Namespace uu____19095 in
        let uu____19097 = open_fact_db_tags env in uu____19094 :: uu____19097 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____19091
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_elt Prims.list *
        FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____19124 = encode_sigelt env se in
      match uu____19124 with
      | (g, env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let (recover_caching_and_update_env :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env ->
    fun decls ->
      FStar_All.pipe_right decls
        (FStar_List.collect
           (fun elt ->
              if
                elt.FStar_SMTEncoding_Term.key = FStar_Pervasives_Native.None
              then [elt]
              else
                (let uu____19170 =
                   let uu____19173 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____19173 in
                 match uu____19170 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None ->
                     ((let uu____19188 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____19188
                         elt);
                      [elt]))))
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv ->
    fun se ->
      let caption decls =
        let uu____19218 = FStar_Options.log_queries () in
        if uu____19218
        then
          let uu____19223 =
            let uu____19224 =
              let uu____19226 =
                let uu____19228 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____19228 (FStar_String.concat ", ") in
              Prims.op_Hat "encoding sigelt " uu____19226 in
            FStar_SMTEncoding_Term.Caption uu____19224 in
          uu____19223 :: decls
        else decls in
      (let uu____19247 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
       if uu____19247
       then
         let uu____19250 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____19250
       else ());
      (let env =
         let uu____19256 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____19256 tcenv in
       let uu____19257 = encode_top_level_facts env se in
       match uu____19257 with
       | (decls, env1) ->
           (set_env env1;
            (let uu____19271 =
               let uu____19274 =
                 let uu____19277 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1) in
                 FStar_All.pipe_right uu____19277
                   FStar_SMTEncoding_Term.decls_list_of in
               caption uu____19274 in
             FStar_SMTEncoding_Z3.giveZ3 uu____19271)))
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env ->
    fun name ->
      fun decls ->
        let caption decls1 =
          let uu____19310 = FStar_Options.log_queries () in
          if uu____19310
          then
            let msg = Prims.op_Hat "Externals for " name in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)] in
        set_env
          (let uu___1744_19330 = env in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1744_19330.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1744_19330.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1744_19330.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1744_19330.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1744_19330.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1744_19330.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1744_19330.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1744_19330.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1744_19330.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1744_19330.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____19335 =
             let uu____19338 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env) in
             FStar_All.pipe_right uu____19338
               FStar_SMTEncoding_Term.decls_list_of in
           caption uu____19335 in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv ->
    fun modul ->
      let uu____19358 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
      if uu____19358
      then ([], [])
      else
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____19391 ->
             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh
               ();
             (let name =
                let uu____19395 =
                  FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                FStar_Util.format2 "%s %s"
                  (if modul.FStar_Syntax_Syntax.is_interface
                   then "interface"
                   else "module") uu____19395 in
              (let uu____19405 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
               if uu____19405
               then
                 let uu____19408 =
                   FStar_All.pipe_right
                     (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                     Prims.string_of_int in
                 FStar_Util.print2
                   "+++++++++++Encoding externals for %s ... %s exports\n"
                   name uu____19408
               else ());
              (let env =
                 let uu____19416 =
                   get_env modul.FStar_Syntax_Syntax.name tcenv in
                 FStar_All.pipe_right uu____19416
                   FStar_SMTEncoding_Env.reset_current_module_fvbs in
               let encode_signature env1 ses =
                 FStar_All.pipe_right ses
                   (FStar_List.fold_left
                      (fun uu____19455 ->
                         fun se ->
                           match uu____19455 with
                           | (g, env2) ->
                               let uu____19475 =
                                 encode_top_level_facts env2 se in
                               (match uu____19475 with
                                | (g', env3) ->
                                    ((FStar_List.append g g'), env3)))
                      ([], env1)) in
               let uu____19498 =
                 encode_signature
                   (let uu___1768_19507 = env in
                    {
                      FStar_SMTEncoding_Env.bvar_bindings =
                        (uu___1768_19507.FStar_SMTEncoding_Env.bvar_bindings);
                      FStar_SMTEncoding_Env.fvar_bindings =
                        (uu___1768_19507.FStar_SMTEncoding_Env.fvar_bindings);
                      FStar_SMTEncoding_Env.depth =
                        (uu___1768_19507.FStar_SMTEncoding_Env.depth);
                      FStar_SMTEncoding_Env.tcenv =
                        (uu___1768_19507.FStar_SMTEncoding_Env.tcenv);
                      FStar_SMTEncoding_Env.warn = false;
                      FStar_SMTEncoding_Env.nolabels =
                        (uu___1768_19507.FStar_SMTEncoding_Env.nolabels);
                      FStar_SMTEncoding_Env.use_zfuel_name =
                        (uu___1768_19507.FStar_SMTEncoding_Env.use_zfuel_name);
                      FStar_SMTEncoding_Env.encode_non_total_function_typ =
                        (uu___1768_19507.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                      FStar_SMTEncoding_Env.current_module_name =
                        (uu___1768_19507.FStar_SMTEncoding_Env.current_module_name);
                      FStar_SMTEncoding_Env.encoding_quantifier =
                        (uu___1768_19507.FStar_SMTEncoding_Env.encoding_quantifier);
                      FStar_SMTEncoding_Env.global_cache =
                        (uu___1768_19507.FStar_SMTEncoding_Env.global_cache)
                    }) modul.FStar_Syntax_Syntax.exports in
               match uu____19498 with
               | (decls, env1) ->
                   (give_decls_to_z3_and_set_env env1 name decls;
                    (let uu____19525 =
                       FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                     if uu____19525
                     then
                       FStar_Util.print1 "Done encoding externals for %s\n"
                         name
                     else ());
                    (let uu____19531 =
                       FStar_All.pipe_right env1
                         FStar_SMTEncoding_Env.get_current_module_fvbs in
                     (decls, uu____19531))))))
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv ->
    fun tcmod ->
      fun uu____19561 ->
        match uu____19561 with
        | (decls, fvbs) ->
            let uu____19574 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
            if uu____19574
            then ()
            else
              (let name =
                 let uu____19581 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu____19581 in
               (let uu____19591 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                if uu____19591
                then
                  let uu____19594 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19594
                else ());
               (let env =
                  let uu____19602 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv in
                  FStar_All.pipe_right uu____19602
                    FStar_SMTEncoding_Env.reset_current_module_fvbs in
                let env1 =
                  let uu____19604 = FStar_All.pipe_right fvbs FStar_List.rev in
                  FStar_All.pipe_right uu____19604
                    (FStar_List.fold_left
                       (fun env1 ->
                          fun fvb ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env) in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19618 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                 if uu____19618
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
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____19680 =
           let uu____19682 = FStar_TypeChecker_Env.current_module tcenv in
           FStar_Ident.string_of_lid uu____19682 in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19680);
        (let env =
           let uu____19684 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____19684 tcenv in
         let uu____19685 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19722 = aux rest in
                 (match uu____19722 with
                  | (out, rest1) ->
                      let t =
                        let uu____19750 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____19750 with
                        | FStar_Pervasives_Native.Some uu____19753 ->
                            let uu____19754 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____19754
                              x.FStar_Syntax_Syntax.sort
                        | uu____19755 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        norm_with_steps
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops]
                          env.FStar_SMTEncoding_Env.tcenv t in
                      let uu____19759 =
                        let uu____19762 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1811_19765 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1811_19765.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1811_19765.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____19762 :: out in
                      (uu____19759, rest1))
             | uu____19770 -> ([], bindings) in
           let uu____19777 = aux tcenv.FStar_TypeChecker_Env.gamma in
           match uu____19777 with
           | (closing, bindings) ->
               let uu____19802 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____19802, bindings) in
         match uu____19685 with
         | (q1, bindings) ->
             let uu____19825 = encode_env_bindings env bindings in
             (match uu____19825 with
              | (env_decls, env1) ->
                  ((let uu____19847 =
                      ((FStar_TypeChecker_Env.debug tcenv
                          FStar_Options.Medium)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____19847
                    then
                      let uu____19854 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula {: %s\n"
                        uu____19854
                    else ());
                   (let uu____19859 =
                      FStar_Util.record_time
                        (fun uu____19874 ->
                           FStar_SMTEncoding_EncodeTerm.encode_formula q1
                             env1) in
                    match uu____19859 with
                    | ((phi, qdecls), ms) ->
                        let uu____19898 =
                          let uu____19903 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19903 phi in
                        (match uu____19898 with
                         | (labels, phi1) ->
                             let uu____19920 = encode_labels labels in
                             (match uu____19920 with
                              | (label_prefix, label_suffix) ->
                                  let caption =
                                    let uu____19956 =
                                      FStar_Options.log_queries () in
                                    if uu____19956
                                    then
                                      let uu____19961 =
                                        let uu____19962 =
                                          let uu____19964 =
                                            FStar_Syntax_Print.term_to_string
                                              q1 in
                                          Prims.op_Hat
                                            "Encoding query formula : "
                                            uu____19964 in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19962 in
                                      [uu____19961]
                                    else [] in
                                  let query_prelude =
                                    let uu____19972 =
                                      let uu____19973 =
                                        let uu____19974 =
                                          let uu____19977 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                          let uu____19984 =
                                            let uu____19987 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial in
                                            FStar_List.append qdecls
                                              uu____19987 in
                                          FStar_List.append uu____19977
                                            uu____19984 in
                                        FStar_List.append env_decls
                                          uu____19974 in
                                      FStar_All.pipe_right uu____19973
                                        (recover_caching_and_update_env env1) in
                                    FStar_All.pipe_right uu____19972
                                      FStar_SMTEncoding_Term.decls_list_of in
                                  let qry =
                                    let uu____19997 =
                                      let uu____20005 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____20006 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query" in
                                      (uu____20005,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____20006) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19997 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  ((let uu____20019 =
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
                                           (FStar_Options.Other "SMTQuery")) in
                                    if uu____20019
                                    then
                                      FStar_Util.print_string
                                        "} Done encoding\n"
                                    else ());
                                   (let uu____20030 =
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
                                           (FStar_Options.Other "Time")) in
                                    if uu____20030
                                    then
                                      FStar_Util.print1
                                        "Encoding took %sms\n"
                                        (Prims.string_of_int ms)
                                    else ());
                                   (query_prelude, labels, qry, suffix))))))))