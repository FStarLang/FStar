open Prims
let (reify_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u  ->
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____18  -> FStar_TypeChecker_Env.reify_comp env c u)
  
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
      let uu____33 =
        let uu____37 =
          let uu____39 =
            FStar_TypeChecker_Env.current_module
              env.FStar_SMTEncoding_Env.tcenv
             in
          FStar_Ident.string_of_lid uu____39  in
        FStar_Pervasives_Native.Some uu____37  in
      FStar_Profiling.profile
        (fun uu____42  ->
           FStar_TypeChecker_Normalize.normalize steps
             env.FStar_SMTEncoding_Env.tcenv t) uu____33
        "FStar.TypeChecker.SMTEncoding.Encode.norm_before_encoding"
  
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        let uu____60 =
          let uu____64 =
            let uu____66 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____66  in
          FStar_Pervasives_Native.Some uu____64  in
        FStar_Profiling.profile
          (fun uu____69  -> FStar_TypeChecker_Normalize.normalize steps env t)
          uu____60 "FStar.TypeChecker.SMTEncoding.Encode.norm"
  
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
  let uu____210 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____210 with
  | (asym,a) ->
      let uu____221 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____221 with
       | (xsym,x) ->
           let uu____232 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____232 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____310 =
                      let uu____322 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____322, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____310  in
                  let xtok = Prims.op_Hat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____342 =
                      let uu____350 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____350)  in
                    FStar_SMTEncoding_Util.mkApp uu____342  in
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
                      let uu____445 =
                        let uu____453 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1  in
                        (uu____453, FStar_Pervasives_Native.None, axiom_name)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____445  in
                    let uu____456 =
                      FStar_List.fold_left
                        (fun uu____510  ->
                           fun var  ->
                             match uu____510 with
                             | (axioms,app,vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var]
                                    in
                                 let vars2 = FStar_List.append vars1 [var]
                                    in
                                 let axiom_name1 =
                                   let uu____637 =
                                     let uu____639 =
                                       let uu____641 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length
                                          in
                                       Prims.string_of_int uu____641  in
                                     Prims.op_Hat "." uu____639  in
                                   Prims.op_Hat axiom_name uu____637  in
                                 let uu____663 =
                                   let uu____666 =
                                     let uu____669 =
                                       let uu____670 =
                                         let uu____678 =
                                           let uu____679 =
                                             let uu____690 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1
                                                in
                                             ([[app1]], vars2, uu____690)  in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____679
                                            in
                                         (uu____678,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1)
                                          in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____670
                                        in
                                     [uu____669]  in
                                   FStar_List.append axioms uu____666  in
                                 (uu____663, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one
                       in
                    match uu____456 with
                    | (axioms,uu____736,uu____737) -> axioms  in
                  let uu____762 =
                    let uu____765 =
                      let uu____768 =
                        let uu____771 =
                          let uu____774 =
                            let uu____775 =
                              let uu____783 =
                                let uu____784 =
                                  let uu____795 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, uu____795)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____784
                                 in
                              (uu____783, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____775  in
                          [uu____774]  in
                        xtok_decl :: uu____771  in
                      xname_decl :: uu____768  in
                    let uu____807 =
                      let uu____810 =
                        let uu____813 =
                          let uu____814 =
                            let uu____822 =
                              let uu____823 =
                                let uu____834 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp)
                                   in
                                ([[xtok_app]], vars, uu____834)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____823
                               in
                            (uu____822,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____814  in
                        [uu____813]  in
                      FStar_List.append tot_fun_axioms uu____810  in
                    FStar_List.append uu____765 uu____807  in
                  (xtok1, (FStar_List.length vars), uu____762)  in
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
                  let uu____1004 =
                    let uu____1025 =
                      let uu____1044 =
                        let uu____1045 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____1045
                         in
                      quant axy uu____1044  in
                    (FStar_Parser_Const.op_Eq, uu____1025)  in
                  let uu____1062 =
                    let uu____1085 =
                      let uu____1106 =
                        let uu____1125 =
                          let uu____1126 =
                            let uu____1127 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____1127  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____1126
                           in
                        quant axy uu____1125  in
                      (FStar_Parser_Const.op_notEq, uu____1106)  in
                    let uu____1144 =
                      let uu____1167 =
                        let uu____1188 =
                          let uu____1207 =
                            let uu____1208 =
                              let uu____1209 =
                                let uu____1214 =
                                  FStar_SMTEncoding_Term.unboxBool x  in
                                let uu____1215 =
                                  FStar_SMTEncoding_Term.unboxBool y  in
                                (uu____1214, uu____1215)  in
                              FStar_SMTEncoding_Util.mkAnd uu____1209  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1208
                             in
                          quant xy uu____1207  in
                        (FStar_Parser_Const.op_And, uu____1188)  in
                      let uu____1232 =
                        let uu____1255 =
                          let uu____1276 =
                            let uu____1295 =
                              let uu____1296 =
                                let uu____1297 =
                                  let uu____1302 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  let uu____1303 =
                                    FStar_SMTEncoding_Term.unboxBool y  in
                                  (uu____1302, uu____1303)  in
                                FStar_SMTEncoding_Util.mkOr uu____1297  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1296
                               in
                            quant xy uu____1295  in
                          (FStar_Parser_Const.op_Or, uu____1276)  in
                        let uu____1320 =
                          let uu____1343 =
                            let uu____1364 =
                              let uu____1383 =
                                let uu____1384 =
                                  let uu____1385 =
                                    FStar_SMTEncoding_Term.unboxBool x  in
                                  FStar_SMTEncoding_Util.mkNot uu____1385  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1384
                                 in
                              quant qx uu____1383  in
                            (FStar_Parser_Const.op_Negation, uu____1364)  in
                          let uu____1402 =
                            let uu____1425 =
                              let uu____1446 =
                                let uu____1465 =
                                  let uu____1466 =
                                    let uu____1467 =
                                      let uu____1472 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1473 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1472, uu____1473)  in
                                    FStar_SMTEncoding_Util.mkLT uu____1467
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1466
                                   in
                                quant xy uu____1465  in
                              (FStar_Parser_Const.op_LT, uu____1446)  in
                            let uu____1490 =
                              let uu____1513 =
                                let uu____1534 =
                                  let uu____1553 =
                                    let uu____1554 =
                                      let uu____1555 =
                                        let uu____1560 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1561 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1560, uu____1561)  in
                                      FStar_SMTEncoding_Util.mkLTE uu____1555
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1554
                                     in
                                  quant xy uu____1553  in
                                (FStar_Parser_Const.op_LTE, uu____1534)  in
                              let uu____1578 =
                                let uu____1601 =
                                  let uu____1622 =
                                    let uu____1641 =
                                      let uu____1642 =
                                        let uu____1643 =
                                          let uu____1648 =
                                            FStar_SMTEncoding_Term.unboxInt x
                                             in
                                          let uu____1649 =
                                            FStar_SMTEncoding_Term.unboxInt y
                                             in
                                          (uu____1648, uu____1649)  in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1643
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1642
                                       in
                                    quant xy uu____1641  in
                                  (FStar_Parser_Const.op_GT, uu____1622)  in
                                let uu____1666 =
                                  let uu____1689 =
                                    let uu____1710 =
                                      let uu____1729 =
                                        let uu____1730 =
                                          let uu____1731 =
                                            let uu____1736 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1737 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1736, uu____1737)  in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1731
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1730
                                         in
                                      quant xy uu____1729  in
                                    (FStar_Parser_Const.op_GTE, uu____1710)
                                     in
                                  let uu____1754 =
                                    let uu____1777 =
                                      let uu____1798 =
                                        let uu____1817 =
                                          let uu____1818 =
                                            let uu____1819 =
                                              let uu____1824 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1825 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1824, uu____1825)  in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1819
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1818
                                           in
                                        quant xy uu____1817  in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1798)
                                       in
                                    let uu____1842 =
                                      let uu____1865 =
                                        let uu____1886 =
                                          let uu____1905 =
                                            let uu____1906 =
                                              let uu____1907 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1907
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1906
                                             in
                                          quant qx uu____1905  in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1886)
                                         in
                                      let uu____1924 =
                                        let uu____1947 =
                                          let uu____1968 =
                                            let uu____1987 =
                                              let uu____1988 =
                                                let uu____1989 =
                                                  let uu____1994 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1995 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1994, uu____1995)
                                                   in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1989
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1988
                                               in
                                            quant xy uu____1987  in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1968)
                                           in
                                        let uu____2012 =
                                          let uu____2035 =
                                            let uu____2056 =
                                              let uu____2075 =
                                                let uu____2076 =
                                                  let uu____2077 =
                                                    let uu____2082 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x
                                                       in
                                                    let uu____2083 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y
                                                       in
                                                    (uu____2082, uu____2083)
                                                     in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____2077
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____2076
                                                 in
                                              quant xy uu____2075  in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____2056)
                                             in
                                          let uu____2100 =
                                            let uu____2123 =
                                              let uu____2144 =
                                                let uu____2163 =
                                                  let uu____2164 =
                                                    let uu____2165 =
                                                      let uu____2170 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x
                                                         in
                                                      let uu____2171 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y
                                                         in
                                                      (uu____2170,
                                                        uu____2171)
                                                       in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____2165
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____2164
                                                   in
                                                quant xy uu____2163  in
                                              (FStar_Parser_Const.op_Division,
                                                uu____2144)
                                               in
                                            let uu____2188 =
                                              let uu____2211 =
                                                let uu____2232 =
                                                  let uu____2251 =
                                                    let uu____2252 =
                                                      let uu____2253 =
                                                        let uu____2258 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x
                                                           in
                                                        let uu____2259 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y
                                                           in
                                                        (uu____2258,
                                                          uu____2259)
                                                         in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____2253
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____2252
                                                     in
                                                  quant xy uu____2251  in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____2232)
                                                 in
                                              let uu____2276 =
                                                let uu____2299 =
                                                  let uu____2320 =
                                                    let uu____2339 =
                                                      let uu____2340 =
                                                        let uu____2341 =
                                                          let uu____2346 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x
                                                             in
                                                          let uu____2347 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y
                                                             in
                                                          (uu____2346,
                                                            uu____2347)
                                                           in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2341
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2340
                                                       in
                                                    quant xy uu____2339  in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2320)
                                                   in
                                                let uu____2364 =
                                                  let uu____2387 =
                                                    let uu____2408 =
                                                      let uu____2427 =
                                                        let uu____2428 =
                                                          let uu____2429 =
                                                            let uu____2434 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x
                                                               in
                                                            let uu____2435 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y
                                                               in
                                                            (uu____2434,
                                                              uu____2435)
                                                             in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2429
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2428
                                                         in
                                                      quant xy uu____2427  in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2408)
                                                     in
                                                  let uu____2452 =
                                                    let uu____2475 =
                                                      let uu____2496 =
                                                        let uu____2515 =
                                                          let uu____2516 =
                                                            let uu____2517 =
                                                              let uu____2522
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x
                                                                 in
                                                              let uu____2523
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y
                                                                 in
                                                              (uu____2522,
                                                                uu____2523)
                                                               in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2517
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2516
                                                           in
                                                        quant xy uu____2515
                                                         in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2496)
                                                       in
                                                    let uu____2540 =
                                                      let uu____2563 =
                                                        let uu____2584 =
                                                          let uu____2603 =
                                                            let uu____2604 =
                                                              let uu____2605
                                                                =
                                                                let uu____2610
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x
                                                                   in
                                                                let uu____2611
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y
                                                                   in
                                                                (uu____2610,
                                                                  uu____2611)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2605
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2604
                                                             in
                                                          quant xy uu____2603
                                                           in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2584)
                                                         in
                                                      let uu____2628 =
                                                        let uu____2651 =
                                                          let uu____2672 =
                                                            let uu____2691 =
                                                              let uu____2692
                                                                =
                                                                let uu____2693
                                                                  =
                                                                  let uu____2698
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                  let uu____2699
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                  (uu____2698,
                                                                    uu____2699)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2693
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2692
                                                               in
                                                            quant xy
                                                              uu____2691
                                                             in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2672)
                                                           in
                                                        let uu____2716 =
                                                          let uu____2739 =
                                                            let uu____2760 =
                                                              let uu____2779
                                                                =
                                                                let uu____2780
                                                                  =
                                                                  let uu____2781
                                                                    =
                                                                    let uu____2786
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2787
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2786,
                                                                    uu____2787)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2781
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2780
                                                                 in
                                                              quant xy
                                                                uu____2779
                                                               in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2760)
                                                             in
                                                          let uu____2804 =
                                                            let uu____2827 =
                                                              let uu____2848
                                                                =
                                                                let uu____2867
                                                                  =
                                                                  let uu____2868
                                                                    =
                                                                    let uu____2869
                                                                    =
                                                                    let uu____2874
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2875
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2874,
                                                                    uu____2875)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2869
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2868
                                                                   in
                                                                quant xy
                                                                  uu____2867
                                                                 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2848)
                                                               in
                                                            let uu____2892 =
                                                              let uu____2915
                                                                =
                                                                let uu____2936
                                                                  =
                                                                  let uu____2955
                                                                    =
                                                                    let uu____2956
                                                                    =
                                                                    let uu____2957
                                                                    =
                                                                    let uu____2962
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x  in
                                                                    let uu____2963
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y  in
                                                                    (uu____2962,
                                                                    uu____2963)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2957
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2956
                                                                     in
                                                                  quant xy
                                                                    uu____2955
                                                                   in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2936)
                                                                 in
                                                              let uu____2980
                                                                =
                                                                let uu____3003
                                                                  =
                                                                  let uu____3024
                                                                    =
                                                                    let uu____3043
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    let uu____3045
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____3045
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____3044
                                                                     in
                                                                    quant qx
                                                                    uu____3043
                                                                     in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____3024)
                                                                   in
                                                                [uu____3003]
                                                                 in
                                                              uu____2915 ::
                                                                uu____2980
                                                               in
                                                            uu____2827 ::
                                                              uu____2892
                                                             in
                                                          uu____2739 ::
                                                            uu____2804
                                                           in
                                                        uu____2651 ::
                                                          uu____2716
                                                         in
                                                      uu____2563 ::
                                                        uu____2628
                                                       in
                                                    uu____2475 :: uu____2540
                                                     in
                                                  uu____2387 :: uu____2452
                                                   in
                                                uu____2299 :: uu____2364  in
                                              uu____2211 :: uu____2276  in
                                            uu____2123 :: uu____2188  in
                                          uu____2035 :: uu____2100  in
                                        uu____1947 :: uu____2012  in
                                      uu____1865 :: uu____1924  in
                                    uu____1777 :: uu____1842  in
                                  uu____1689 :: uu____1754  in
                                uu____1601 :: uu____1666  in
                              uu____1513 :: uu____1578  in
                            uu____1425 :: uu____1490  in
                          uu____1343 :: uu____1402  in
                        uu____1255 :: uu____1320  in
                      uu____1167 :: uu____1232  in
                    uu____1085 :: uu____1144  in
                  uu____1004 :: uu____1062  in
                let mk l v =
                  let uu____3584 =
                    let uu____3596 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____3686  ->
                              match uu____3686 with
                              | (l',uu____3707) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____3596
                      (FStar_Option.map
                         (fun uu____3806  ->
                            match uu____3806 with
                            | (uu____3834,b) ->
                                let uu____3868 = FStar_Ident.range_of_lid l
                                   in
                                b uu____3868 v))
                     in
                  FStar_All.pipe_right uu____3584 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____3951  ->
                          match uu____3951 with
                          | (l',uu____3972) -> FStar_Ident.lid_equals l l'))
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
          let uu____4046 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____4046 with
          | (xxsym,xx) ->
              let uu____4057 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____4057 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____4073 =
                     let uu____4081 =
                       let uu____4082 =
                         let uu____4093 =
                           let uu____4094 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____4104 =
                             let uu____4115 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____4115 :: vars  in
                           uu____4094 :: uu____4104  in
                         let uu____4141 =
                           let uu____4142 =
                             let uu____4147 =
                               let uu____4148 =
                                 let uu____4153 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____4153)  in
                               FStar_SMTEncoding_Util.mkEq uu____4148  in
                             (xx_has_type, uu____4147)  in
                           FStar_SMTEncoding_Util.mkImp uu____4142  in
                         ([[xx_has_type]], uu____4093, uu____4141)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____4082  in
                     let uu____4166 =
                       let uu____4168 =
                         let uu____4170 =
                           let uu____4172 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.op_Hat "_pretyping_" uu____4172  in
                         Prims.op_Hat module_name uu____4170  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____4168
                        in
                     (uu____4081, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____4166)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____4073)
  
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
    let uu____4228 =
      let uu____4230 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____4230  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____4228  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____4252 =
      let uu____4253 =
        let uu____4261 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____4261, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4253  in
    let uu____4266 =
      let uu____4269 =
        let uu____4270 =
          let uu____4278 =
            let uu____4279 =
              let uu____4290 =
                let uu____4291 =
                  let uu____4296 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____4296)  in
                FStar_SMTEncoding_Util.mkImp uu____4291  in
              ([[typing_pred]], [xx], uu____4290)  in
            let uu____4321 =
              let uu____4336 = FStar_TypeChecker_Env.get_range env  in
              let uu____4337 = mkForall_fuel env  in uu____4337 uu____4336
               in
            uu____4321 uu____4279  in
          (uu____4278, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4270  in
      [uu____4269]  in
    uu____4252 :: uu____4266  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____4384 =
      let uu____4385 =
        let uu____4393 =
          let uu____4394 = FStar_TypeChecker_Env.get_range env  in
          let uu____4395 =
            let uu____4406 =
              let uu____4411 =
                let uu____4414 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____4414]  in
              [uu____4411]  in
            let uu____4419 =
              let uu____4420 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4420 tt  in
            (uu____4406, [bb], uu____4419)  in
          FStar_SMTEncoding_Term.mkForall uu____4394 uu____4395  in
        (uu____4393, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4385  in
    let uu____4445 =
      let uu____4448 =
        let uu____4449 =
          let uu____4457 =
            let uu____4458 =
              let uu____4469 =
                let uu____4470 =
                  let uu____4475 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____4475)  in
                FStar_SMTEncoding_Util.mkImp uu____4470  in
              ([[typing_pred]], [xx], uu____4469)  in
            let uu____4502 =
              let uu____4517 = FStar_TypeChecker_Env.get_range env  in
              let uu____4518 = mkForall_fuel env  in uu____4518 uu____4517
               in
            uu____4502 uu____4458  in
          (uu____4457, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4449  in
      [uu____4448]  in
    uu____4384 :: uu____4445  in
  let mk_int env nm tt =
    let lex_t =
      let uu____4561 =
        let uu____4562 =
          let uu____4568 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4568, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4562  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4561  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____4582 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4582  in
    let uu____4587 =
      let uu____4588 =
        let uu____4596 =
          let uu____4597 = FStar_TypeChecker_Env.get_range env  in
          let uu____4598 =
            let uu____4609 =
              let uu____4614 =
                let uu____4617 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____4617]  in
              [uu____4614]  in
            let uu____4622 =
              let uu____4623 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4623 tt  in
            (uu____4609, [bb], uu____4622)  in
          FStar_SMTEncoding_Term.mkForall uu____4597 uu____4598  in
        (uu____4596, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4588  in
    let uu____4648 =
      let uu____4651 =
        let uu____4652 =
          let uu____4660 =
            let uu____4661 =
              let uu____4672 =
                let uu____4673 =
                  let uu____4678 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____4678)  in
                FStar_SMTEncoding_Util.mkImp uu____4673  in
              ([[typing_pred]], [xx], uu____4672)  in
            let uu____4705 =
              let uu____4720 = FStar_TypeChecker_Env.get_range env  in
              let uu____4721 = mkForall_fuel env  in uu____4721 uu____4720
               in
            uu____4705 uu____4661  in
          (uu____4660, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4652  in
      let uu____4743 =
        let uu____4746 =
          let uu____4747 =
            let uu____4755 =
              let uu____4756 =
                let uu____4767 =
                  let uu____4768 =
                    let uu____4773 =
                      let uu____4774 =
                        let uu____4777 =
                          let uu____4780 =
                            let uu____4783 =
                              let uu____4784 =
                                let uu____4789 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____4790 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero
                                   in
                                (uu____4789, uu____4790)  in
                              FStar_SMTEncoding_Util.mkGT uu____4784  in
                            let uu____4792 =
                              let uu____4795 =
                                let uu____4796 =
                                  let uu____4801 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____4802 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero
                                     in
                                  (uu____4801, uu____4802)  in
                                FStar_SMTEncoding_Util.mkGTE uu____4796  in
                              let uu____4804 =
                                let uu____4807 =
                                  let uu____4808 =
                                    let uu____4813 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____4814 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____4813, uu____4814)  in
                                  FStar_SMTEncoding_Util.mkLT uu____4808  in
                                [uu____4807]  in
                              uu____4795 :: uu____4804  in
                            uu____4783 :: uu____4792  in
                          typing_pred_y :: uu____4780  in
                        typing_pred :: uu____4777  in
                      FStar_SMTEncoding_Util.mk_and_l uu____4774  in
                    (uu____4773, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____4768  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4767)
                 in
              let uu____4847 =
                let uu____4862 = FStar_TypeChecker_Env.get_range env  in
                let uu____4863 = mkForall_fuel env  in uu____4863 uu____4862
                 in
              uu____4847 uu____4756  in
            (uu____4755,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____4747  in
        [uu____4746]  in
      uu____4651 :: uu____4743  in
    uu____4587 :: uu____4648  in
  let mk_real env nm tt =
    let lex_t =
      let uu____4906 =
        let uu____4907 =
          let uu____4913 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____4913, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____4907  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4906  in
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
      let uu____4929 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4929  in
    let uu____4934 =
      let uu____4935 =
        let uu____4943 =
          let uu____4944 = FStar_TypeChecker_Env.get_range env  in
          let uu____4945 =
            let uu____4956 =
              let uu____4961 =
                let uu____4964 = FStar_SMTEncoding_Term.boxReal b  in
                [uu____4964]  in
              [uu____4961]  in
            let uu____4969 =
              let uu____4970 = FStar_SMTEncoding_Term.boxReal b  in
              FStar_SMTEncoding_Term.mk_HasType uu____4970 tt  in
            (uu____4956, [bb], uu____4969)  in
          FStar_SMTEncoding_Term.mkForall uu____4944 uu____4945  in
        (uu____4943, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4935  in
    let uu____4995 =
      let uu____4998 =
        let uu____4999 =
          let uu____5007 =
            let uu____5008 =
              let uu____5019 =
                let uu____5020 =
                  let uu____5025 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x
                     in
                  (typing_pred, uu____5025)  in
                FStar_SMTEncoding_Util.mkImp uu____5020  in
              ([[typing_pred]], [xx], uu____5019)  in
            let uu____5052 =
              let uu____5067 = FStar_TypeChecker_Env.get_range env  in
              let uu____5068 = mkForall_fuel env  in uu____5068 uu____5067
               in
            uu____5052 uu____5008  in
          (uu____5007, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4999  in
      let uu____5090 =
        let uu____5093 =
          let uu____5094 =
            let uu____5102 =
              let uu____5103 =
                let uu____5114 =
                  let uu____5115 =
                    let uu____5120 =
                      let uu____5121 =
                        let uu____5124 =
                          let uu____5127 =
                            let uu____5130 =
                              let uu____5131 =
                                let uu____5136 =
                                  FStar_SMTEncoding_Term.unboxReal x  in
                                let uu____5137 =
                                  FStar_SMTEncoding_Util.mkReal "0.0"  in
                                (uu____5136, uu____5137)  in
                              FStar_SMTEncoding_Util.mkGT uu____5131  in
                            let uu____5139 =
                              let uu____5142 =
                                let uu____5143 =
                                  let uu____5148 =
                                    FStar_SMTEncoding_Term.unboxReal y  in
                                  let uu____5149 =
                                    FStar_SMTEncoding_Util.mkReal "0.0"  in
                                  (uu____5148, uu____5149)  in
                                FStar_SMTEncoding_Util.mkGTE uu____5143  in
                              let uu____5151 =
                                let uu____5154 =
                                  let uu____5155 =
                                    let uu____5160 =
                                      FStar_SMTEncoding_Term.unboxReal y  in
                                    let uu____5161 =
                                      FStar_SMTEncoding_Term.unboxReal x  in
                                    (uu____5160, uu____5161)  in
                                  FStar_SMTEncoding_Util.mkLT uu____5155  in
                                [uu____5154]  in
                              uu____5142 :: uu____5151  in
                            uu____5130 :: uu____5139  in
                          typing_pred_y :: uu____5127  in
                        typing_pred :: uu____5124  in
                      FStar_SMTEncoding_Util.mk_and_l uu____5121  in
                    (uu____5120, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____5115  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____5114)
                 in
              let uu____5194 =
                let uu____5209 = FStar_TypeChecker_Env.get_range env  in
                let uu____5210 = mkForall_fuel env  in uu____5210 uu____5209
                 in
              uu____5194 uu____5103  in
            (uu____5102,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real")
             in
          FStar_SMTEncoding_Util.mkAssume uu____5094  in
        [uu____5093]  in
      uu____4998 :: uu____5090  in
    uu____4934 :: uu____4995  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____5257 =
      let uu____5258 =
        let uu____5266 =
          let uu____5267 = FStar_TypeChecker_Env.get_range env  in
          let uu____5268 =
            let uu____5279 =
              let uu____5284 =
                let uu____5287 = FStar_SMTEncoding_Term.boxString b  in
                [uu____5287]  in
              [uu____5284]  in
            let uu____5292 =
              let uu____5293 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____5293 tt  in
            (uu____5279, [bb], uu____5292)  in
          FStar_SMTEncoding_Term.mkForall uu____5267 uu____5268  in
        (uu____5266, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5258  in
    let uu____5318 =
      let uu____5321 =
        let uu____5322 =
          let uu____5330 =
            let uu____5331 =
              let uu____5342 =
                let uu____5343 =
                  let uu____5348 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____5348)  in
                FStar_SMTEncoding_Util.mkImp uu____5343  in
              ([[typing_pred]], [xx], uu____5342)  in
            let uu____5375 =
              let uu____5390 = FStar_TypeChecker_Env.get_range env  in
              let uu____5391 = mkForall_fuel env  in uu____5391 uu____5390
               in
            uu____5375 uu____5331  in
          (uu____5330, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____5322  in
      [uu____5321]  in
    uu____5257 :: uu____5318  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____5438 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____5438]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____5468 =
      let uu____5469 =
        let uu____5477 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____5477, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5469  in
    [uu____5468]  in
  let mk_and_interp env conj uu____5500 =
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
    let uu____5529 =
      let uu____5530 =
        let uu____5538 =
          let uu____5539 = FStar_TypeChecker_Env.get_range env  in
          let uu____5540 =
            let uu____5551 =
              let uu____5552 =
                let uu____5557 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____5557, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5552  in
            ([[l_and_a_b]], [aa; bb], uu____5551)  in
          FStar_SMTEncoding_Term.mkForall uu____5539 uu____5540  in
        (uu____5538, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5530  in
    [uu____5529]  in
  let mk_or_interp env disj uu____5612 =
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
    let uu____5641 =
      let uu____5642 =
        let uu____5650 =
          let uu____5651 = FStar_TypeChecker_Env.get_range env  in
          let uu____5652 =
            let uu____5663 =
              let uu____5664 =
                let uu____5669 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____5669, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5664  in
            ([[l_or_a_b]], [aa; bb], uu____5663)  in
          FStar_SMTEncoding_Term.mkForall uu____5651 uu____5652  in
        (uu____5650, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5642  in
    [uu____5641]  in
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
    let uu____5747 =
      let uu____5748 =
        let uu____5756 =
          let uu____5757 = FStar_TypeChecker_Env.get_range env  in
          let uu____5758 =
            let uu____5769 =
              let uu____5770 =
                let uu____5775 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5775, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5770  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5769)  in
          FStar_SMTEncoding_Term.mkForall uu____5757 uu____5758  in
        (uu____5756, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5748  in
    [uu____5747]  in
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
    let uu____5865 =
      let uu____5866 =
        let uu____5874 =
          let uu____5875 = FStar_TypeChecker_Env.get_range env  in
          let uu____5876 =
            let uu____5887 =
              let uu____5888 =
                let uu____5893 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____5893, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____5888  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5887)  in
          FStar_SMTEncoding_Term.mkForall uu____5875 uu____5876  in
        (uu____5874, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5866  in
    [uu____5865]  in
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
    let uu____5993 =
      let uu____5994 =
        let uu____6002 =
          let uu____6003 = FStar_TypeChecker_Env.get_range env  in
          let uu____6004 =
            let uu____6015 =
              let uu____6016 =
                let uu____6021 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____6021, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____6016  in
            ([[l_imp_a_b]], [aa; bb], uu____6015)  in
          FStar_SMTEncoding_Term.mkForall uu____6003 uu____6004  in
        (uu____6002, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5994  in
    [uu____5993]  in
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
    let uu____6105 =
      let uu____6106 =
        let uu____6114 =
          let uu____6115 = FStar_TypeChecker_Env.get_range env  in
          let uu____6116 =
            let uu____6127 =
              let uu____6128 =
                let uu____6133 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____6133, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____6128  in
            ([[l_iff_a_b]], [aa; bb], uu____6127)  in
          FStar_SMTEncoding_Term.mkForall uu____6115 uu____6116  in
        (uu____6114, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6106  in
    [uu____6105]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____6204 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____6204  in
    let uu____6209 =
      let uu____6210 =
        let uu____6218 =
          let uu____6219 = FStar_TypeChecker_Env.get_range env  in
          let uu____6220 =
            let uu____6231 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____6231)  in
          FStar_SMTEncoding_Term.mkForall uu____6219 uu____6220  in
        (uu____6218, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6210  in
    [uu____6209]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____6284 =
      let uu____6285 =
        let uu____6293 =
          let uu____6294 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____6294 range_ty  in
        let uu____6295 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____6293, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____6295)
         in
      FStar_SMTEncoding_Util.mkAssume uu____6285  in
    [uu____6284]  in
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
        let uu____6341 = FStar_SMTEncoding_Term.n_fuel Prims.int_one  in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____6341 x1 t  in
      let uu____6343 = FStar_TypeChecker_Env.get_range env  in
      let uu____6344 =
        let uu____6355 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____6355)  in
      FStar_SMTEncoding_Term.mkForall uu____6343 uu____6344  in
    let uu____6380 =
      let uu____6381 =
        let uu____6389 =
          let uu____6390 = FStar_TypeChecker_Env.get_range env  in
          let uu____6391 =
            let uu____6402 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____6402)  in
          FStar_SMTEncoding_Term.mkForall uu____6390 uu____6391  in
        (uu____6389,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6381  in
    [uu____6380]  in
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
    let uu____6463 =
      let uu____6464 =
        let uu____6472 =
          let uu____6473 = FStar_TypeChecker_Env.get_range env  in
          let uu____6474 =
            let uu____6490 =
              let uu____6491 =
                let uu____6496 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____6497 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____6496, uu____6497)  in
              FStar_SMTEncoding_Util.mkAnd uu____6491  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu____6490)
             in
          FStar_SMTEncoding_Term.mkForall' uu____6473 uu____6474  in
        (uu____6472,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____6464  in
    [uu____6463]  in
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
          let uu____7055 =
            FStar_Util.find_opt
              (fun uu____7093  ->
                 match uu____7093 with
                 | (l,uu____7109) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____7055 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____7152,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7213 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____7213 with
        | (form,decls) ->
            let uu____7222 =
              let uu____7225 =
                let uu____7228 =
                  let uu____7229 =
                    let uu____7237 =
                      let uu____7238 =
                        let uu____7240 = FStar_Ident.string_of_lid lid  in
                        Prims.op_Hat "Lemma: " uu____7240  in
                      FStar_Pervasives_Native.Some uu____7238  in
                    let uu____7244 =
                      let uu____7246 = FStar_Ident.string_of_lid lid  in
                      Prims.op_Hat "lemma_" uu____7246  in
                    (form, uu____7237, uu____7244)  in
                  FStar_SMTEncoding_Util.mkAssume uu____7229  in
                [uu____7228]  in
              FStar_All.pipe_right uu____7225
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____7222
  
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
              let uu____7304 =
                ((let uu____7308 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____7308) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____7304
              then
                let arg_sorts =
                  let uu____7320 =
                    let uu____7321 = FStar_Syntax_Subst.compress t_norm  in
                    uu____7321.FStar_Syntax_Syntax.n  in
                  match uu____7320 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7327) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____7365  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____7372 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____7374 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____7374 with
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
                    let uu____7406 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____7406, env1)
              else
                (let uu____7411 = prims.is lid  in
                 if uu____7411
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____7420 = prims.mk lid vname  in
                   match uu____7420 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____7444 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____7444, env1)
                 else
                   (let encode_non_total_function_typ =
                      let uu____7451 = FStar_Ident.nsstr lid  in
                      uu____7451 <> "Prims"  in
                    let uu____7455 =
                      let uu____7474 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____7474 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____7500 =
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____7500
                            then
                              let uu____7503 =
                                reify_comp
                                  (let uu___320_7506 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___320_7506.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___320_7506.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___320_7506.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___320_7506.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___320_7506.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___320_7506.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___320_7506.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___320_7506.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___320_7506.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___320_7506.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___320_7506.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___320_7506.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___320_7506.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___320_7506.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___320_7506.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___320_7506.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___320_7506.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___320_7506.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___320_7506.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___320_7506.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___320_7506.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___320_7506.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___320_7506.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___320_7506.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___320_7506.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___320_7506.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___320_7506.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___320_7506.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___320_7506.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___320_7506.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___320_7506.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___320_7506.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___320_7506.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___320_7506.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___320_7506.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___320_7506.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___320_7506.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___320_7506.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___320_7506.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___320_7506.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___320_7506.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___320_7506.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___320_7506.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___320_7506.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___320_7506.FStar_TypeChecker_Env.erasable_types_tab)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____7503
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____7529 =
                              FStar_Syntax_Unionfind.with_uf_enabled
                                (fun uu____7543  ->
                                   FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                     env.FStar_SMTEncoding_Env.tcenv comp1)
                               in
                            (args, uu____7529)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____7455 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_7643  ->
                                  match uu___0_7643 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____7647 = FStar_Util.prefix vars
                                         in
                                      (match uu____7647 with
                                       | (uu____7680,xxv) ->
                                           let xx =
                                             let uu____7719 =
                                               let uu____7720 =
                                                 let uu____7726 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7726,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7720
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7719
                                              in
                                           let uu____7729 =
                                             let uu____7730 =
                                               let uu____7738 =
                                                 let uu____7739 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7740 =
                                                   let uu____7751 =
                                                     let uu____7752 =
                                                       let uu____7757 =
                                                         let uu____7758 =
                                                           let uu____7759 =
                                                             let uu____7761 =
                                                               FStar_Ident.string_of_lid
                                                                 d
                                                                in
                                                             FStar_SMTEncoding_Env.escape
                                                               uu____7761
                                                              in
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             uu____7759 xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____7758
                                                          in
                                                       (vapp, uu____7757)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____7752
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7751)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7739 uu____7740
                                                  in
                                               let uu____7771 =
                                                 let uu____7773 =
                                                   let uu____7775 =
                                                     FStar_Ident.string_of_lid
                                                       d
                                                      in
                                                   FStar_SMTEncoding_Env.escape
                                                     uu____7775
                                                    in
                                                 Prims.op_Hat
                                                   "disc_equation_"
                                                   uu____7773
                                                  in
                                               (uu____7738,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 uu____7771)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7730
                                              in
                                           [uu____7729])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____7783 = FStar_Util.prefix vars
                                         in
                                      (match uu____7783 with
                                       | (uu____7816,xxv) ->
                                           let xx =
                                             let uu____7855 =
                                               let uu____7856 =
                                                 let uu____7862 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____7862,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____7856
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____7855
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
                                           let uu____7873 =
                                             let uu____7874 =
                                               let uu____7882 =
                                                 let uu____7883 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____7884 =
                                                   let uu____7895 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____7895)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____7883 uu____7884
                                                  in
                                               (uu____7882,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____7874
                                              in
                                           [uu____7873])
                                  | uu____7908 -> []))
                           in
                        let uu____7909 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____7909 with
                         | (vars,guards,env',decls1,uu____7934) ->
                             let uu____7947 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7960 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____7960, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____7964 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____7964 with
                                    | (g,ds) ->
                                        let uu____7977 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____7977,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____7947 with
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
                                  let should_thunk uu____8000 =
                                    let is_type t =
                                      let uu____8008 =
                                        let uu____8009 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____8009.FStar_Syntax_Syntax.n  in
                                      match uu____8008 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____8013 -> true
                                      | uu____8015 -> false  in
                                    let is_squash t =
                                      let uu____8024 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____8024 with
                                      | (head,uu____8043) ->
                                          let uu____8068 =
                                            let uu____8069 =
                                              FStar_Syntax_Util.un_uinst head
                                               in
                                            uu____8069.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____8068 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____8074;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____8075;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____8077;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____8078;_};_},uu____8079)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____8087 -> false)
                                       in
                                    (((let uu____8091 = FStar_Ident.nsstr lid
                                          in
                                       uu____8091 <> "Prims") &&
                                        (let uu____8096 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____8096))
                                       &&
                                       (let uu____8102 = is_squash t_norm  in
                                        Prims.op_Negation uu____8102))
                                      &&
                                      (let uu____8105 = is_type t_norm  in
                                       Prims.op_Negation uu____8105)
                                     in
                                  let uu____8107 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____8166 -> (false, vars)  in
                                  (match uu____8107 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____8216 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____8216 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____8248 =
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
                                              | uu____8269 ->
                                                  let uu____8278 =
                                                    let uu____8286 =
                                                      get_vtok ()  in
                                                    (uu____8286, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8278
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____8293 =
                                                let uu____8301 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____8301)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____8293
                                               in
                                            let uu____8315 =
                                              let vname_decl =
                                                let uu____8323 =
                                                  let uu____8335 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____8335,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____8323
                                                 in
                                              let uu____8346 =
                                                let env2 =
                                                  let uu___416_8352 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___416_8352.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____8353 =
                                                  let uu____8355 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____8355
                                                   in
                                                if uu____8353
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____8346 with
                                              | (tok_typing,decls2) ->
                                                  let uu____8372 =
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
                                                        let uu____8398 =
                                                          let uu____8401 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8401
                                                           in
                                                        let uu____8408 =
                                                          let uu____8409 =
                                                            let uu____8412 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, [])
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun uu____8418
                                                                  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____8418)
                                                              uu____8412
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____8409
                                                           in
                                                        (uu____8398,
                                                          uu____8408)
                                                    | uu____8421 when thunked
                                                        -> (decls2, env1)
                                                    | uu____8434 ->
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
                                                          let uu____8458 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____8459 =
                                                            let uu____8470 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____8470)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____8458
                                                            uu____8459
                                                           in
                                                        let name_tok_corr =
                                                          let uu____8480 =
                                                            let uu____8488 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____8488,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8480
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
                                                            let uu____8499 =
                                                              let uu____8500
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____8500]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____8499
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____8527 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8528 =
                                                              let uu____8539
                                                                =
                                                                let uu____8540
                                                                  =
                                                                  let uu____8545
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____8546
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____8545,
                                                                    uu____8546)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____8540
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____8539)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8527
                                                              uu____8528
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____8575 =
                                                          let uu____8578 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8578
                                                           in
                                                        (uu____8575, env1)
                                                     in
                                                  (match uu____8372 with
                                                   | (tok_decl,env2) ->
                                                       let uu____8599 =
                                                         let uu____8602 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____8602
                                                           tok_decl
                                                          in
                                                       (uu____8599, env2))
                                               in
                                            (match uu____8315 with
                                             | (decls2,env2) ->
                                                 let uu____8621 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____8631 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____8631 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____8646 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____8646, decls)
                                                    in
                                                 (match uu____8621 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____8661 =
                                                          let uu____8669 =
                                                            let uu____8670 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8671 =
                                                              let uu____8682
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____8682)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____8670
                                                              uu____8671
                                                             in
                                                          (uu____8669,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8661
                                                         in
                                                      let freshness =
                                                        let uu____8698 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____8698
                                                        then
                                                          let uu____8706 =
                                                            let uu____8707 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____8708 =
                                                              let uu____8721
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____8728
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____8721,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____8728)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____8707
                                                              uu____8708
                                                             in
                                                          let uu____8734 =
                                                            let uu____8737 =
                                                              let uu____8738
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____8738
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____8737]  in
                                                          uu____8706 ::
                                                            uu____8734
                                                        else []  in
                                                      let g =
                                                        let uu____8744 =
                                                          let uu____8747 =
                                                            let uu____8750 =
                                                              let uu____8753
                                                                =
                                                                let uu____8756
                                                                  =
                                                                  let uu____8759
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____8759
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____8756
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8753
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____8750
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____8747
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____8744
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
          let uu____8799 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8799 with
          | FStar_Pervasives_Native.None  ->
              let uu____8810 = encode_free_var false env x t t_norm []  in
              (match uu____8810 with
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
            let uu____8873 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____8873 with
            | (decls,env1) ->
                let uu____8884 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____8884
                then
                  let uu____8891 =
                    let uu____8892 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____8892  in
                  (uu____8891, env1)
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
             (fun uu____8948  ->
                fun lb  ->
                  match uu____8948 with
                  | (decls,env1) ->
                      let uu____8968 =
                        let uu____8973 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____8973
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8968 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____9002 = FStar_Syntax_Util.head_and_args t  in
    match uu____9002 with
    | (hd,args) ->
        let uu____9046 =
          let uu____9047 = FStar_Syntax_Util.un_uinst hd  in
          uu____9047.FStar_Syntax_Syntax.n  in
        (match uu____9046 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____9053,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             let uu____9076 = FStar_Ident.string_of_lid effect_name  in
             FStar_Util.starts_with "FStar.Tactics" uu____9076
         | uu____9079 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____9090 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___500_9098 = en  in
    let uu____9099 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___500_9098.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___500_9098.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___500_9098.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___500_9098.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___500_9098.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___500_9098.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___500_9098.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___500_9098.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___500_9098.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___500_9098.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____9099
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____9129  ->
      fun quals  ->
        match uu____9129 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____9234 = FStar_Util.first_N nbinders formals  in
              match uu____9234 with
              | (formals1,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____9331  ->
                         fun uu____9332  ->
                           match (uu____9331, uu____9332) with
                           | ((formal,uu____9358),(binder,uu____9360)) ->
                               let uu____9381 =
                                 let uu____9388 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____9388)  in
                               FStar_Syntax_Syntax.NT uu____9381) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____9402 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____9443  ->
                              match uu____9443 with
                              | (x,i) ->
                                  let uu____9462 =
                                    let uu___526_9463 = x  in
                                    let uu____9464 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___526_9463.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___526_9463.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____9464
                                    }  in
                                  (uu____9462, i)))
                       in
                    FStar_All.pipe_right uu____9402
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____9488 =
                      let uu____9493 = FStar_Syntax_Subst.compress body  in
                      let uu____9494 =
                        let uu____9495 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____9495
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____9493 uu____9494
                       in
                    uu____9488 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___533_9544 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___533_9544.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___533_9544.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___533_9544.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___533_9544.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___533_9544.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___533_9544.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___533_9544.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___533_9544.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___533_9544.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___533_9544.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___533_9544.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___533_9544.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___533_9544.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___533_9544.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___533_9544.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___533_9544.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___533_9544.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___533_9544.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___533_9544.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___533_9544.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___533_9544.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___533_9544.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___533_9544.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___533_9544.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___533_9544.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___533_9544.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___533_9544.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___533_9544.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___533_9544.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___533_9544.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___533_9544.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___533_9544.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___533_9544.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___533_9544.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___533_9544.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___533_9544.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___533_9544.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___533_9544.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___533_9544.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___533_9544.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___533_9544.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___533_9544.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___533_9544.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___533_9544.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___533_9544.FStar_TypeChecker_Env.erasable_types_tab)
                }  in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu____9616  ->
                       fun uu____9617  ->
                         match (uu____9616, uu____9617) with
                         | ((x,uu____9643),(b,uu____9645)) ->
                             let uu____9666 =
                               let uu____9673 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____9673)  in
                             FStar_Syntax_Syntax.NT uu____9666) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst comp  in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu____9698 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____9698
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____9727 ->
                    let uu____9734 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm uu____9734
                | uu____9735 when Prims.op_Negation norm ->
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
                | uu____9738 ->
                    let uu____9739 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____9739)
                 in
              let aux t1 e1 =
                let uu____9781 = FStar_Syntax_Util.abs_formals e1  in
                match uu____9781 with
                | (binders,body,lopt) ->
                    let uu____9813 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____9829 -> arrow_formals_comp_norm false t1  in
                    (match uu____9813 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____9863 =
                           if nformals < nbinders
                           then
                             let uu____9897 =
                               FStar_Util.first_N nformals binders  in
                             match uu____9897 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____9977 = subst_comp formals bs0 comp
                                    in
                                 (bs0, body1, uu____9977)
                           else
                             if nformals > nbinders
                             then
                               (let uu____10007 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____10007 with
                                | (binders1,body1) ->
                                    let uu____10060 =
                                      subst_comp formals binders1 comp  in
                                    (binders1, body1, uu____10060))
                             else
                               (let uu____10073 =
                                  subst_comp formals binders comp  in
                                (binders, body, uu____10073))
                            in
                         (match uu____9863 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____10133 = aux t e  in
              match uu____10133 with
              | (binders,body,comp) ->
                  let uu____10179 =
                    let uu____10190 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp
                       in
                    if uu____10190
                    then
                      let comp1 =
                        reify_comp tcenv comp FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_Syntax_Unionfind.with_uf_enabled
                          (fun uu____10206  ->
                             FStar_TypeChecker_Util.reify_body tcenv [] body)
                         in
                      let uu____10207 = aux comp1 body1  in
                      match uu____10207 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____10179 with
                   | (binders1,body1,comp1) ->
                       let uu____10290 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____10290, comp1))
               in
            (try
               (fun uu___604_10317  ->
                  match () with
                  | () ->
                      let uu____10324 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____10324
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____10340 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____10403  ->
                                   fun lb  ->
                                     match uu____10403 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____10458 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____10458
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____10464 =
                                             let uu____10473 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____10473
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____10464 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____10340 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____10614;
                                    FStar_Syntax_Syntax.lbeff = uu____10615;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____10617;
                                    FStar_Syntax_Syntax.lbpos = uu____10618;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____10642 =
                                     let uu____10649 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____10649 with
                                     | (tcenv',uu____10665,e_t) ->
                                         let uu____10671 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____10682 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____10671 with
                                          | (e1,t_norm1) ->
                                              ((let uu___667_10699 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___667_10699.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____10642 with
                                    | (env',e1,t_norm1) ->
                                        let uu____10709 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____10709 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____10729 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____10729
                                               then
                                                 let uu____10734 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____10737 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____10734 uu____10737
                                               else ());
                                              (let uu____10742 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____10742 with
                                               | (vars,_guards,env'1,binder_decls,uu____10769)
                                                   ->
                                                   let uu____10782 =
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
                                                         let uu____10799 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____10799
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____10821 =
                                                          let uu____10822 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____10823 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____10822 fvb
                                                            uu____10823
                                                           in
                                                        (vars, uu____10821))
                                                      in
                                                   (match uu____10782 with
                                                    | (vars1,app) ->
                                                        let uu____10834 =
                                                          let is_logical =
                                                            let uu____10847 =
                                                              let uu____10848
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____10848.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____10847
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____10854 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____10858 =
                                                              let uu____10859
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____10859
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____10858
                                                              (fun lid  ->
                                                                 let uu____10868
                                                                   =
                                                                   let uu____10869
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid  in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu____10869
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____10868
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____10870 =
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
                                                          if uu____10870
                                                          then
                                                            let uu____10886 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____10887 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app,
                                                              uu____10886,
                                                              uu____10887)
                                                          else
                                                            (let uu____10898
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____10898))
                                                           in
                                                        (match uu____10834
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____10922
                                                                 =
                                                                 let uu____10930
                                                                   =
                                                                   let uu____10931
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____10932
                                                                    =
                                                                    let uu____10943
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____10943)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____10931
                                                                    uu____10932
                                                                    in
                                                                 let uu____10952
                                                                   =
                                                                   let uu____10953
                                                                    =
                                                                    let uu____10955
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid  in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu____10955
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____10953
                                                                    in
                                                                 (uu____10930,
                                                                   uu____10952,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____10922
                                                                in
                                                             let uu____10961
                                                               =
                                                               let uu____10964
                                                                 =
                                                                 let uu____10967
                                                                   =
                                                                   let uu____10970
                                                                    =
                                                                    let uu____10973
                                                                    =
                                                                    let uu____10976
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____10976
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____10973
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____10970
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____10967
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____10964
                                                                in
                                                             (uu____10961,
                                                               env2)))))))
                               | uu____10985 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____11045 =
                                   let uu____11051 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____11051,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____11045  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____11057 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____11110  ->
                                         fun fvb  ->
                                           match uu____11110 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____11165 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11165
                                                  in
                                               let gtok =
                                                 let uu____11169 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____11169
                                                  in
                                               let env4 =
                                                 let uu____11172 =
                                                   let uu____11175 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun uu____11181  ->
                                                        FStar_Pervasives_Native.Some
                                                          uu____11181)
                                                     uu____11175
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____11172
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____11057 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____11301
                                     t_norm uu____11303 =
                                     match (uu____11301, uu____11303) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____11333;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____11334;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____11336;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____11337;_})
                                         ->
                                         let uu____11364 =
                                           let uu____11371 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____11371 with
                                           | (tcenv',uu____11387,e_t) ->
                                               let uu____11393 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____11404 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____11393 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___754_11421 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___754_11421.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____11364 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____11434 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____11434
                                                then
                                                  let uu____11439 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____11441 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____11443 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____11439 uu____11441
                                                    uu____11443
                                                else ());
                                               (let uu____11448 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____11448 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____11475 =
                                                      FStar_Syntax_Unionfind.with_uf_enabled
                                                        (fun uu____11489  ->
                                                           FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                             env3.FStar_SMTEncoding_Env.tcenv
                                                             tres_comp)
                                                       in
                                                    (match uu____11475 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____11505 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____11505
                                                           then
                                                             let uu____11510
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____11512
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____11515
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____11517
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____11510
                                                               uu____11512
                                                               uu____11515
                                                               uu____11517
                                                           else ());
                                                          (let uu____11522 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____11522
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____11551)
                                                               ->
                                                               let uu____11564
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____11577
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____11577,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____11581
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____11581
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____11594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____11594,
                                                                    decls0))
                                                                  in
                                                               (match uu____11564
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
                                                                    let uu____11615
                                                                    =
                                                                    let uu____11627
                                                                    =
                                                                    let uu____11630
                                                                    =
                                                                    let uu____11633
                                                                    =
                                                                    let uu____11636
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____11636
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____11633
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____11630
                                                                     in
                                                                    (g,
                                                                    uu____11627,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____11615
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
                                                                    let uu____11666
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____11666
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
                                                                    let uu____11681
                                                                    =
                                                                    let uu____11684
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____11684
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11681
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____11690
                                                                    =
                                                                    let uu____11693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____11693
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11690
                                                                     in
                                                                    let uu____11698
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____11698
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____11714
                                                                    =
                                                                    let uu____11722
                                                                    =
                                                                    let uu____11723
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11724
                                                                    =
                                                                    let uu____11740
                                                                    =
                                                                    let uu____11741
                                                                    =
                                                                    let uu____11746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____11746)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11741
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11740)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____11723
                                                                    uu____11724
                                                                     in
                                                                    let uu____11760
                                                                    =
                                                                    let uu____11761
                                                                    =
                                                                    let uu____11763
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu____11763
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____11761
                                                                     in
                                                                    (uu____11722,
                                                                    uu____11760,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11714
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____11770
                                                                    =
                                                                    let uu____11778
                                                                    =
                                                                    let uu____11779
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11780
                                                                    =
                                                                    let uu____11791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____11791)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11779
                                                                    uu____11780
                                                                     in
                                                                    (uu____11778,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11770
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____11805
                                                                    =
                                                                    let uu____11813
                                                                    =
                                                                    let uu____11814
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11815
                                                                    =
                                                                    let uu____11826
                                                                    =
                                                                    let uu____11827
                                                                    =
                                                                    let uu____11832
                                                                    =
                                                                    let uu____11833
                                                                    =
                                                                    let uu____11836
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero
                                                                     in
                                                                    uu____11836
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____11833
                                                                     in
                                                                    (gsapp,
                                                                    uu____11832)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____11827
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11826)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11814
                                                                    uu____11815
                                                                     in
                                                                    (uu____11813,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11805
                                                                     in
                                                                    let uu____11850
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
                                                                    let uu____11862
                                                                    =
                                                                    let uu____11863
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11863
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____11862
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu____11867
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11867
                                                                     in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars  in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11876
                                                                     ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1  in
                                                                    let uu____11877
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu____11877
                                                                     in
                                                                    let uu____11879
                                                                    =
                                                                    let uu____11887
                                                                    =
                                                                    let uu____11888
                                                                    =
                                                                    let uu____11893
                                                                    =
                                                                    let uu____11894
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11895
                                                                    =
                                                                    let uu____11906
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11906)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11894
                                                                    uu____11895
                                                                     in
                                                                    (uu____11893,
                                                                    tot_fun_axioms)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____11888
                                                                     in
                                                                    (uu____11887,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11879
                                                                     in
                                                                    let uu____11919
                                                                    =
                                                                    let uu____11928
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____11928
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11943
                                                                    =
                                                                    let uu____11946
                                                                    =
                                                                    let uu____11947
                                                                    =
                                                                    let uu____11955
                                                                    =
                                                                    let uu____11956
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11957
                                                                    =
                                                                    let uu____11968
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____11968)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11956
                                                                    uu____11957
                                                                     in
                                                                    (uu____11955,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11947
                                                                     in
                                                                    [uu____11946]
                                                                     in
                                                                    (d3,
                                                                    uu____11943)
                                                                     in
                                                                    match uu____11919
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____11850
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____12025
                                                                    =
                                                                    let uu____12028
                                                                    =
                                                                    let uu____12031
                                                                    =
                                                                    let uu____12034
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____12034
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____12031
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____12028
                                                                     in
                                                                    let uu____12041
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____12025,
                                                                    uu____12041,
                                                                    env02))))))))))
                                      in
                                   let uu____12046 =
                                     let uu____12059 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____12122  ->
                                          fun uu____12123  ->
                                            match (uu____12122, uu____12123)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____12248 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____12248 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____12059
                                      in
                                   (match uu____12046 with
                                    | (decls2,eqns,env01) ->
                                        let uu____12315 =
                                          let isDeclFun uu___1_12332 =
                                            match uu___1_12332 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12334 -> true
                                            | uu____12347 -> false  in
                                          let uu____12349 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____12349
                                            (fun decls3  ->
                                               let uu____12379 =
                                                 FStar_List.fold_left
                                                   (fun uu____12410  ->
                                                      fun elt  ->
                                                        match uu____12410
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____12451 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____12451
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____12479
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____12479
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
                                                                    let uu___853_12517
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___853_12517.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___853_12517.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___853_12517.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____12379 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____12549 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____12549, elts, rest))
                                           in
                                        (match uu____12315 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____12578 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_12584  ->
                                        match uu___2_12584 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____12587 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____12595 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____12595)))
                                in
                             if uu____12578
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___870_12617  ->
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
                                      let uu____12662 = FStar_List.hd names
                                         in
                                      FStar_All.pipe_right uu____12662
                                        FStar_Pervasives_Native.snd
                                       in
                                    ((let uu____12680 =
                                        let uu____12690 =
                                          let uu____12698 =
                                            let uu____12700 =
                                              let uu____12702 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names
                                                 in
                                              FStar_All.pipe_right
                                                uu____12702
                                                (FStar_String.concat ",")
                                               in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____12700
                                              (if plural
                                               then "their"
                                               else "its")
                                             in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____12698, r)
                                           in
                                        [uu____12690]  in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____12680);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12761 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12761
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____12780 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____12780, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12836 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____12836 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l  in
      let uu____12842 = encode_sigelt' env se  in
      match uu____12842 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12854 =
                  let uu____12857 =
                    let uu____12858 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12858  in
                  [uu____12857]  in
                FStar_All.pipe_right uu____12854
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____12863 ->
                let uu____12864 =
                  let uu____12867 =
                    let uu____12870 =
                      let uu____12871 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12871  in
                    [uu____12870]  in
                  FStar_All.pipe_right uu____12867
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____12878 =
                  let uu____12881 =
                    let uu____12884 =
                      let uu____12887 =
                        let uu____12888 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____12888  in
                      [uu____12887]  in
                    FStar_All.pipe_right uu____12884
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____12881  in
                FStar_List.append uu____12864 uu____12878
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____12902 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12902
       then
         let uu____12907 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____12907
       else ());
      (let is_opaque_to_smt t =
         let uu____12919 =
           let uu____12920 = FStar_Syntax_Subst.compress t  in
           uu____12920.FStar_Syntax_Syntax.n  in
         match uu____12919 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12925)) -> s = "opaque_to_smt"
         | uu____12930 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____12939 =
           let uu____12940 = FStar_Syntax_Subst.compress t  in
           uu____12940.FStar_Syntax_Syntax.n  in
         match uu____12939 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____12945)) -> s = "uninterpreted_by_smt"
         | uu____12950 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____12956 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu____12968 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____12986 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12987 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____13000 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____13001 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____13013 =
             let uu____13015 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____13015  in
           if uu____13013
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____13044 ->
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
                  let uu____13077 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn  in
                  norm_before_encoding env1 uu____13077  in
                let uu____13078 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____13078 with
                | (formals,uu____13090) ->
                    let arity = FStar_List.length formals  in
                    let uu____13098 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____13098 with
                     | (aname,atok,env2) ->
                         let uu____13120 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2
                            in
                         (match uu____13120 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____13136 =
                                  let uu____13137 =
                                    let uu____13149 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____13169  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____13149,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____13137
                                   in
                                [uu____13136;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____13186 =
                                let aux uu____13232 uu____13233 =
                                  match (uu____13232, uu____13233) with
                                  | ((bv,uu____13277),(env3,acc_sorts,acc))
                                      ->
                                      let uu____13309 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____13309 with
                                       | (xxsym,xx,env4) ->
                                           let uu____13332 =
                                             let uu____13335 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____13335 :: acc_sorts  in
                                           (env4, uu____13332, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____13186 with
                               | (uu____13367,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____13383 =
                                       let uu____13391 =
                                         let uu____13392 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13393 =
                                           let uu____13404 =
                                             let uu____13405 =
                                               let uu____13410 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____13410)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____13405
                                              in
                                           ([[app]], xs_sorts, uu____13404)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13392 uu____13393
                                          in
                                       (uu____13391,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13383
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____13425 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____13425
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____13428 =
                                       let uu____13436 =
                                         let uu____13437 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____13438 =
                                           let uu____13449 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____13449)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13437 uu____13438
                                          in
                                       (uu____13436,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13428
                                      in
                                   let uu____13462 =
                                     let uu____13465 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____13465  in
                                   (env2, uu____13462))))
                 in
              let uu____13474 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____13474 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13500,uu____13501)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____13502 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4))
              in
           (match uu____13502 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13524,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____13531 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_13537  ->
                       match uu___3_13537 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____13540 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____13546 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____13549 -> false))
                in
             Prims.op_Negation uu____13531  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____13559 =
                let uu____13564 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____13564 env fv t quals  in
              match uu____13559 with
              | (decls,env1) ->
                  let tname = FStar_Ident.string_of_lid lid  in
                  let tsym =
                    let uu____13578 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid  in
                    FStar_Option.get uu____13578  in
                  let uu____13581 =
                    let uu____13582 =
                      let uu____13585 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____13585
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____13582  in
                  (uu____13581, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____13595 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____13595 with
            | (uvs,f1) ->
                let env1 =
                  let uu___1013_13607 = env  in
                  let uu____13608 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1013_13607.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1013_13607.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1013_13607.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____13608;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1013_13607.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1013_13607.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1013_13607.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1013_13607.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1013_13607.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1013_13607.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1013_13607.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 = norm_before_encoding env1 f1  in
                let uu____13610 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____13610 with
                 | (f3,decls) ->
                     let g =
                       let uu____13624 =
                         let uu____13627 =
                           let uu____13628 =
                             let uu____13636 =
                               let uu____13637 =
                                 let uu____13639 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____13639
                                  in
                               FStar_Pervasives_Native.Some uu____13637  in
                             let uu____13643 =
                               let uu____13645 =
                                 let uu____13647 =
                                   FStar_Ident.string_of_lid l  in
                                 Prims.op_Hat "assumption_" uu____13647  in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu____13645
                                in
                             (f3, uu____13636, uu____13643)  in
                           FStar_SMTEncoding_Util.mkAssume uu____13628  in
                         [uu____13627]  in
                       FStar_All.pipe_right uu____13624
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____13656) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____13670 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____13692 =
                        let uu____13695 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____13695.FStar_Syntax_Syntax.fv_name  in
                      uu____13692.FStar_Syntax_Syntax.v  in
                    let uu____13696 =
                      let uu____13698 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____13698  in
                    if uu____13696
                    then
                      let val_decl =
                        let uu___1030_13730 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1030_13730.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1030_13730.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1030_13730.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1030_13730.FStar_Syntax_Syntax.sigopts)
                        }  in
                      let uu____13731 = encode_sigelt' env1 val_decl  in
                      match uu____13731 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____13670 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____13767,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                           FStar_Syntax_Syntax.lbunivs = uu____13769;
                           FStar_Syntax_Syntax.lbtyp = uu____13770;
                           FStar_Syntax_Syntax.lbeff = uu____13771;
                           FStar_Syntax_Syntax.lbdef = uu____13772;
                           FStar_Syntax_Syntax.lbattrs = uu____13773;
                           FStar_Syntax_Syntax.lbpos = uu____13774;_}::[]),uu____13775)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu____13794 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one
              in
           (match uu____13794 with
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
                  let uu____13832 =
                    let uu____13835 =
                      let uu____13836 =
                        let uu____13844 =
                          let uu____13845 =
                            FStar_Syntax_Syntax.range_of_fv b2t  in
                          let uu____13846 =
                            let uu____13857 =
                              let uu____13858 =
                                let uu____13863 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____13863)  in
                              FStar_SMTEncoding_Util.mkEq uu____13858  in
                            ([[b2t_x]], [xx], uu____13857)  in
                          FStar_SMTEncoding_Term.mkForall uu____13845
                            uu____13846
                           in
                        (uu____13844,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____13836  in
                    [uu____13835]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____13832
                   in
                let uu____13901 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____13901, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____13904,uu____13905) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_13915  ->
                   match uu___4_13915 with
                   | FStar_Syntax_Syntax.Discriminator uu____13917 -> true
                   | uu____13919 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____13921,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____13933 =
                      let uu____13935 =
                        let uu____13936 = FStar_Ident.ns_of_lid l  in
                        FStar_List.hd uu____13936  in
                      FStar_Ident.text_of_id uu____13935  in
                    uu____13933 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_13945  ->
                      match uu___5_13945 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____13948 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13951) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_13965  ->
                   match uu___6_13965 with
                   | FStar_Syntax_Syntax.Projector uu____13967 -> true
                   | uu____13973 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____13977 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____13977 with
            | FStar_Pervasives_Native.Some uu____13984 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___1095_13986 = se  in
                  let uu____13987 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____13987;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1095_13986.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1095_13986.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1095_13986.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1095_13986.FStar_Syntax_Syntax.sigopts)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13990) ->
           let bindings1 =
             FStar_List.map
               (fun lb  ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef  in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu___1107_14011 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1107_14011.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1107_14011.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1107_14011.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1107_14011.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1107_14011.FStar_Syntax_Syntax.lbpos)
                  }) bindings
              in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14016) ->
           let uu____14025 = encode_sigelts env ses  in
           (match uu____14025 with
            | (g,env1) ->
                let uu____14036 =
                  FStar_List.fold_left
                    (fun uu____14060  ->
                       fun elt  ->
                         match uu____14060 with
                         | (g',inversions) ->
                             let uu____14088 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_14111  ->
                                       match uu___7_14111 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____14113;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____14114;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____14115;_}
                                           -> false
                                       | uu____14122 -> true))
                                in
                             (match uu____14088 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1133_14147 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1133_14147.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1133_14147.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1133_14147.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____14036 with
                 | (g',inversions) ->
                     let uu____14166 =
                       FStar_List.fold_left
                         (fun uu____14197  ->
                            fun elt  ->
                              match uu____14197 with
                              | (decls,elts,rest) ->
                                  let uu____14238 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_14247  ->
                                            match uu___8_14247 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____14249 -> true
                                            | uu____14262 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____14238
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____14285 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_14306  ->
                                               match uu___9_14306 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____14308 -> true
                                               | uu____14321 -> false))
                                        in
                                     match uu____14285 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1155_14352 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1155_14352.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1155_14352.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1155_14352.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____14166 with
                      | (decls,elts,rest) ->
                          let uu____14378 =
                            let uu____14379 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____14386 =
                              let uu____14389 =
                                let uu____14392 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____14392  in
                              FStar_List.append elts uu____14389  in
                            FStar_List.append uu____14379 uu____14386  in
                          (uu____14378, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,universe_names,tps,k,uu____14403,datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv  in
           let is_injective =
             let uu____14416 =
               FStar_Syntax_Subst.univ_var_opening universe_names  in
             match uu____14416 with
             | (usubst,uvs) ->
                 let uu____14436 =
                   let uu____14443 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs  in
                   let uu____14444 =
                     FStar_Syntax_Subst.subst_binders usubst tps  in
                   let uu____14445 =
                     let uu____14446 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst
                        in
                     FStar_Syntax_Subst.subst uu____14446 k  in
                   (uu____14443, uu____14444, uu____14445)  in
                 (match uu____14436 with
                  | (env1,tps1,k1) ->
                      let uu____14459 = FStar_Syntax_Subst.open_term tps1 k1
                         in
                      (match uu____14459 with
                       | (tps2,k2) ->
                           let uu____14467 =
                             FStar_Syntax_Util.arrow_formals k2  in
                           (match uu____14467 with
                            | (uu____14475,k3) ->
                                let uu____14481 =
                                  FStar_Syntax_Unionfind.with_uf_enabled
                                    (fun uu____14499  ->
                                       FStar_TypeChecker_TcTerm.tc_binders
                                         env1 tps2)
                                   in
                                (match uu____14481 with
                                 | (tps3,env_tps,uu____14503,us) ->
                                     let u_k =
                                       let uu____14506 =
                                         let uu____14507 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____14508 =
                                           let uu____14513 =
                                             FStar_Syntax_Syntax.fvar t
                                               (FStar_Syntax_Syntax.Delta_constant_at_level
                                                  Prims.int_zero)
                                               FStar_Pervasives_Native.None
                                              in
                                           let uu____14515 =
                                             let uu____14516 =
                                               FStar_Syntax_Util.args_of_binders
                                                 tps3
                                                in
                                             FStar_Pervasives_Native.snd
                                               uu____14516
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____14513 uu____14515
                                            in
                                         uu____14508
                                           FStar_Pervasives_Native.None
                                           uu____14507
                                          in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____14506 k3
                                        in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero
                                          ,uu____14534) -> true
                                       | (FStar_Syntax_Syntax.U_succ
                                          u0,FStar_Syntax_Syntax.U_succ v0)
                                           -> universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          u0,FStar_Syntax_Syntax.U_name v0)
                                           -> FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____14540,FStar_Syntax_Syntax.U_succ
                                          v0) -> universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max
                                          us1,uu____14543) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1  -> universe_leq u1 v))
                                       | (uu____14551,FStar_Syntax_Syntax.U_max
                                          vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown
                                          ,uu____14558) ->
                                           let uu____14559 =
                                             let uu____14561 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14561
                                              in
                                           failwith uu____14559
                                       | (uu____14565,FStar_Syntax_Syntax.U_unknown
                                          ) ->
                                           let uu____14566 =
                                             let uu____14568 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14568
                                              in
                                           failwith uu____14566
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____14572,uu____14573) ->
                                           let uu____14584 =
                                             let uu____14586 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14586
                                              in
                                           failwith uu____14584
                                       | (uu____14590,FStar_Syntax_Syntax.U_unif
                                          uu____14591) ->
                                           let uu____14602 =
                                             let uu____14604 =
                                               FStar_Ident.string_of_lid t
                                                in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____14604
                                              in
                                           failwith uu____14602
                                       | uu____14608 -> false  in
                                     let u_leq_u_k u =
                                       let uu____14621 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u
                                          in
                                       universe_leq uu____14621 u_k  in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____14639 = u_leq_u_k u_tp  in
                                       if uu____14639
                                       then true
                                       else
                                         (let uu____14646 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp
                                             in
                                          match uu____14646 with
                                          | (formals,uu____14655) ->
                                              let uu____14660 =
                                                FStar_Syntax_Unionfind.with_uf_enabled
                                                  (fun uu____14678  ->
                                                     FStar_TypeChecker_TcTerm.tc_binders
                                                       env_tps formals)
                                                 in
                                              (match uu____14660 with
                                               | (uu____14680,uu____14681,uu____14682,u_formals)
                                                   ->
                                                   FStar_Util.for_all
                                                     (fun u_formal  ->
                                                        u_leq_u_k u_formal)
                                                     u_formals))
                                        in
                                     FStar_List.forall2 tp_ok tps3 us))))
              in
           ((let uu____14693 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____14693
             then
               let uu____14698 = FStar_Ident.string_of_lid t  in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____14698
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals  in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_14718  ->
                       match uu___10_14718 with
                       | FStar_Syntax_Syntax.Logic  -> true
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____14722 -> false))
                in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____14735 = c  in
                 match uu____14735 with
                 | (name,args,uu____14740,uu____14741,uu____14742) ->
                     let uu____14753 =
                       let uu____14754 =
                         let uu____14766 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____14793  ->
                                   match uu____14793 with
                                   | (uu____14802,sort,uu____14804) -> sort))
                            in
                         (name, uu____14766,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None)
                          in
                       FStar_SMTEncoding_Term.DeclFun uu____14754  in
                     [uu____14753]
               else
                 (let uu____14815 = FStar_Ident.range_of_lid t  in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____14815 c)
                in
             let inversion_axioms tapp vars =
               let uu____14833 =
                 FStar_SMTEncoding_Env.fresh_fvar
                   env.FStar_SMTEncoding_Env.current_module_name "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____14833 with
               | (xxsym,xx) ->
                   let uu____14846 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14883  ->
                             fun l  ->
                               match uu____14883 with
                               | (out,decls) ->
                                   let data_t =
                                     FStar_TypeChecker_Env.lookup_datacon_noinst
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   let uu____14904 =
                                     FStar_Syntax_Util.arrow_formals data_t
                                      in
                                   (match uu____14904 with
                                    | (args,res) ->
                                        let indices =
                                          let uu____14924 =
                                            let uu____14925 =
                                              FStar_Syntax_Subst.compress res
                                               in
                                            uu____14925.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14924 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____14928,indices) ->
                                              indices
                                          | uu____14954 -> []  in
                                        let env1 =
                                          FStar_All.pipe_right args
                                            (FStar_List.fold_left
                                               (fun env1  ->
                                                  fun uu____14984  ->
                                                    match uu____14984 with
                                                    | (x,uu____14992) ->
                                                        let uu____14997 =
                                                          let uu____14998 =
                                                            let uu____15006 =
                                                              FStar_SMTEncoding_Env.mk_term_projector_name
                                                                l x
                                                               in
                                                            (uu____15006,
                                                              [xx])
                                                             in
                                                          FStar_SMTEncoding_Util.mkApp
                                                            uu____14998
                                                           in
                                                        FStar_SMTEncoding_Env.push_term_var
                                                          env1 x uu____14997)
                                               env)
                                           in
                                        let uu____15011 =
                                          FStar_SMTEncoding_EncodeTerm.encode_args
                                            indices env1
                                           in
                                        (match uu____15011 with
                                         | (indices1,decls') ->
                                             (if
                                                (FStar_List.length indices1)
                                                  <> (FStar_List.length vars)
                                              then failwith "Impossible"
                                              else ();
                                              (let eqs =
                                                 if is_injective
                                                 then
                                                   FStar_List.map2
                                                     (fun v  ->
                                                        fun a  ->
                                                          let uu____15046 =
                                                            let uu____15051 =
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                v
                                                               in
                                                            (uu____15051, a)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____15046) vars
                                                     indices1
                                                 else []  in
                                               let uu____15054 =
                                                 let uu____15055 =
                                                   let uu____15060 =
                                                     let uu____15061 =
                                                       let uu____15066 =
                                                         FStar_SMTEncoding_Env.mk_data_tester
                                                           env1 l xx
                                                          in
                                                       let uu____15067 =
                                                         FStar_All.pipe_right
                                                           eqs
                                                           FStar_SMTEncoding_Util.mk_and_l
                                                          in
                                                       (uu____15066,
                                                         uu____15067)
                                                        in
                                                     FStar_SMTEncoding_Util.mkAnd
                                                       uu____15061
                                                      in
                                                   (out, uu____15060)  in
                                                 FStar_SMTEncoding_Util.mkOr
                                                   uu____15055
                                                  in
                                               (uu____15054,
                                                 (FStar_List.append decls
                                                    decls')))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____14846 with
                    | (data_ax,decls) ->
                        let uu____15082 =
                          FStar_SMTEncoding_Env.fresh_fvar
                            env.FStar_SMTEncoding_Env.current_module_name "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____15082 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if (FStar_List.length datas) > Prims.int_one
                                 then
                                   let uu____15099 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____15099 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____15106 =
                                 let uu____15114 =
                                   let uu____15115 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____15116 =
                                     let uu____15127 =
                                       let uu____15128 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (ffsym,
                                             FStar_SMTEncoding_Term.Fuel_sort)
                                          in
                                       let uu____15130 =
                                         let uu____15133 =
                                           FStar_SMTEncoding_Term.mk_fv
                                             (xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         uu____15133 :: vars  in
                                       FStar_SMTEncoding_Env.add_fuel
                                         uu____15128 uu____15130
                                        in
                                     let uu____15135 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____15127,
                                       uu____15135)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____15115 uu____15116
                                    in
                                 let uu____15144 =
                                   let uu____15146 =
                                     let uu____15148 =
                                       FStar_Ident.string_of_lid t  in
                                     Prims.op_Hat "fuel_guarded_inversion_"
                                       uu____15148
                                      in
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     uu____15146
                                    in
                                 (uu____15114,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____15144)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____15106
                                in
                             let uu____15154 =
                               FStar_All.pipe_right [fuel_guarded_inversion]
                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                in
                             FStar_List.append decls uu____15154))
                in
             let uu____15161 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____15175 ->
                     let uu____15176 =
                       let uu____15183 =
                         let uu____15184 =
                           let uu____15199 = FStar_Syntax_Syntax.mk_Total k
                              in
                           (tps, uu____15199)  in
                         FStar_Syntax_Syntax.Tm_arrow uu____15184  in
                       FStar_Syntax_Syntax.mk uu____15183  in
                     uu____15176 FStar_Pervasives_Native.None
                       k.FStar_Syntax_Syntax.pos
                  in
               let k2 = norm_before_encoding env k1  in
               FStar_Syntax_Util.arrow_formals k2  in
             match uu____15161 with
             | (formals,res) ->
                 let uu____15223 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env
                    in
                 (match uu____15223 with
                  | (vars,guards,env',binder_decls,uu____15248) ->
                      let arity = FStar_List.length vars  in
                      let uu____15262 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity
                         in
                      (match uu____15262 with
                       | (tname,ttok,env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards
                              in
                           let tapp =
                             let uu____15288 =
                               let uu____15296 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               (tname, uu____15296)  in
                             FStar_SMTEncoding_Util.mkApp uu____15288  in
                           let uu____15302 =
                             let tname_decl =
                               let uu____15312 =
                                 let uu____15313 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv  ->
                                           let uu____15332 =
                                             let uu____15334 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv
                                                in
                                             Prims.op_Hat tname uu____15334
                                              in
                                           let uu____15336 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv
                                              in
                                           (uu____15332, uu____15336, false)))
                                    in
                                 let uu____15340 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     ()
                                    in
                                 (tname, uu____15313,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____15340, false)
                                  in
                               constructor_or_logic_type_decl uu____15312  in
                             let uu____15348 =
                               match vars with
                               | [] ->
                                   let uu____15361 =
                                     let uu____15362 =
                                       let uu____15365 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, [])
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____15371  ->
                                            FStar_Pervasives_Native.Some
                                              uu____15371) uu____15365
                                        in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____15362
                                      in
                                   ([], uu____15361)
                               | uu____15374 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token"))
                                      in
                                   let ttok_fresh =
                                     let uu____15384 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____15384
                                      in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars
                                      in
                                   let pats = [[ttok_app]; [tapp]]  in
                                   let name_tok_corr =
                                     let uu____15400 =
                                       let uu____15408 =
                                         let uu____15409 =
                                           FStar_Ident.range_of_lid t  in
                                         let uu____15410 =
                                           let uu____15426 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp)
                                              in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____15426)
                                            in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____15409 uu____15410
                                          in
                                       (uu____15408,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____15400
                                      in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1)
                                in
                             match uu____15348 with
                             | (tok_decls,env2) ->
                                 let uu____15453 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid
                                    in
                                 if uu____15453
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2)
                              in
                           (match uu____15302 with
                            | (decls,env2) ->
                                let kindingAx =
                                  let uu____15481 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp
                                     in
                                  match uu____15481 with
                                  | (k1,decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____15503 =
                                            let uu____15504 =
                                              let uu____15512 =
                                                let uu____15513 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm
                                                   in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____15513
                                                 in
                                              (uu____15512,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok))
                                               in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____15504
                                             in
                                          [uu____15503]
                                        else []  in
                                      let rng = FStar_Ident.range_of_lid t
                                         in
                                      let tot_fun_axioms =
                                        let uu____15523 =
                                          FStar_List.map
                                            (fun uu____15527  ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars
                                           in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____15523 true
                                         in
                                      let uu____15529 =
                                        let uu____15532 =
                                          let uu____15535 =
                                            let uu____15538 =
                                              let uu____15539 =
                                                let uu____15547 =
                                                  let uu____15548 =
                                                    let uu____15553 =
                                                      let uu____15554 =
                                                        let uu____15565 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____15565)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____15554
                                                       in
                                                    (tot_fun_axioms,
                                                      uu____15553)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____15548
                                                   in
                                                (uu____15547,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok))
                                                 in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____15539
                                               in
                                            [uu____15538]  in
                                          FStar_List.append karr uu____15535
                                           in
                                        FStar_All.pipe_right uu____15532
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append decls1 uu____15529
                                   in
                                let aux =
                                  let uu____15584 =
                                    let uu____15587 =
                                      inversion_axioms tapp vars  in
                                    let uu____15590 =
                                      let uu____15593 =
                                        let uu____15596 =
                                          let uu____15597 =
                                            FStar_Ident.range_of_lid t  in
                                          pretype_axiom uu____15597 env2 tapp
                                            vars
                                           in
                                        [uu____15596]  in
                                      FStar_All.pipe_right uu____15593
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append uu____15587 uu____15590
                                     in
                                  FStar_List.append kindingAx uu____15584  in
                                let g =
                                  let uu____15605 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial
                                     in
                                  FStar_List.append uu____15605
                                    (FStar_List.append binder_decls aux)
                                   in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15613,uu____15614,uu____15615,uu____15616,uu____15617)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____15625,t,uu____15627,n_tps,uu____15629) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let t1 = norm_before_encoding env t  in
           let uu____15640 = FStar_Syntax_Util.arrow_formals t1  in
           (match uu____15640 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____15664 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____15664 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____15688 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____15688 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____15708 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____15708 with
                           | (vars,guards,env',binder_decls,names) ->
                               let fields =
                                 FStar_All.pipe_right names
                                   (FStar_List.mapi
                                      (fun n  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____15787 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____15787,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____15794 =
                                   let uu____15795 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____15795, true)
                                    in
                                 let uu____15803 =
                                   let uu____15810 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____15810
                                    in
                                 FStar_All.pipe_right uu____15794 uu____15803
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
                               let uu____15822 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm
                                  in
                               (match uu____15822 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____15834::uu____15835 ->
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
                                            let uu____15884 =
                                              let uu____15885 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____15885]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____15884
                                             in
                                          let uu____15911 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____15912 =
                                            let uu____15923 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____15923)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____15911 uu____15912
                                      | uu____15950 -> tok_typing  in
                                    let uu____15961 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____15961 with
                                     | (vars',guards',env'',decls_formals,uu____15986)
                                         ->
                                         let uu____15999 =
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
                                         (match uu____15999 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____16029 ->
                                                    let uu____16030 =
                                                      let uu____16031 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____16031
                                                       in
                                                    [uu____16030]
                                                 in
                                              let encode_elim uu____16047 =
                                                let uu____16048 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____16048 with
                                                | (head,args) ->
                                                    let uu____16099 =
                                                      let uu____16100 =
                                                        FStar_Syntax_Subst.compress
                                                          head
                                                         in
                                                      uu____16100.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____16099 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____16112;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____16113;_},uu____16114)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____16120 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16120
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
                                                                  | uu____16183
                                                                    ->
                                                                    let uu____16184
                                                                    =
                                                                    let uu____16190
                                                                    =
                                                                    let uu____16192
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16192
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16190)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16184
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16215
                                                                    =
                                                                    let uu____16217
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16217
                                                                     in
                                                                    if
                                                                    uu____16215
                                                                    then
                                                                    let uu____16239
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16239]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16242
                                                                =
                                                                let uu____16256
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16313
                                                                     ->
                                                                    fun
                                                                    uu____16314
                                                                     ->
                                                                    match 
                                                                    (uu____16313,
                                                                    uu____16314)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16425
                                                                    =
                                                                    let uu____16433
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16433
                                                                     in
                                                                    (match uu____16425
                                                                    with
                                                                    | 
                                                                    (uu____16447,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16458
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16458
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16463
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16463
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
                                                                  uu____16256
                                                                 in
                                                              (match uu____16242
                                                               with
                                                               | (uu____16484,arg_vars,elim_eqns_or_guards,uu____16487)
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
                                                                    let uu____16514
                                                                    =
                                                                    let uu____16522
                                                                    =
                                                                    let uu____16523
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16524
                                                                    =
                                                                    let uu____16535
                                                                    =
                                                                    let uu____16536
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16536
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16538
                                                                    =
                                                                    let uu____16539
                                                                    =
                                                                    let uu____16544
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____16544)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16539
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16535,
                                                                    uu____16538)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16523
                                                                    uu____16524
                                                                     in
                                                                    (uu____16522,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16514
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____16559
                                                                    =
                                                                    let uu____16560
                                                                    =
                                                                    let uu____16566
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____16566,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____16560
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____16559
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____16572
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
                                                                    (let uu____16595
                                                                    =
                                                                    let uu____16596
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____16596
                                                                    dapp1  in
                                                                    [uu____16595])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____16572
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____16603
                                                                    =
                                                                    let uu____16611
                                                                    =
                                                                    let uu____16612
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____16613
                                                                    =
                                                                    let uu____16624
                                                                    =
                                                                    let uu____16625
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____16625
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____16627
                                                                    =
                                                                    let uu____16628
                                                                    =
                                                                    let uu____16633
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____16633)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16628
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16624,
                                                                    uu____16627)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____16612
                                                                    uu____16613
                                                                     in
                                                                    (uu____16611,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16603
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
                                                         let uu____16652 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____16652
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
                                                                  | uu____16715
                                                                    ->
                                                                    let uu____16716
                                                                    =
                                                                    let uu____16722
                                                                    =
                                                                    let uu____16724
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16724
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____16722)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____16716
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16747
                                                                    =
                                                                    let uu____16749
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16749
                                                                     in
                                                                    if
                                                                    uu____16747
                                                                    then
                                                                    let uu____16771
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____16771]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____16774
                                                                =
                                                                let uu____16788
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____16845
                                                                     ->
                                                                    fun
                                                                    uu____16846
                                                                     ->
                                                                    match 
                                                                    (uu____16845,
                                                                    uu____16846)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16957
                                                                    =
                                                                    let uu____16965
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____16965
                                                                     in
                                                                    (match uu____16957
                                                                    with
                                                                    | 
                                                                    (uu____16979,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16990
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____16990
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____16995
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
                                                                  uu____16788
                                                                 in
                                                              (match uu____16774
                                                               with
                                                               | (uu____17016,arg_vars,elim_eqns_or_guards,uu____17019)
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
                                                                    let uu____17046
                                                                    =
                                                                    let uu____17054
                                                                    =
                                                                    let uu____17055
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17056
                                                                    =
                                                                    let uu____17067
                                                                    =
                                                                    let uu____17068
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17068
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17070
                                                                    =
                                                                    let uu____17071
                                                                    =
                                                                    let uu____17076
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____17076)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17071
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17067,
                                                                    uu____17070)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17055
                                                                    uu____17056
                                                                     in
                                                                    (uu____17054,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17046
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____17091
                                                                    =
                                                                    let uu____17092
                                                                    =
                                                                    let uu____17098
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____17098,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____17092
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____17091
                                                                     in
                                                                    let prec
                                                                    =
                                                                    let uu____17104
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
                                                                    (let uu____17127
                                                                    =
                                                                    let uu____17128
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____17128
                                                                    dapp1  in
                                                                    [uu____17127])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____17104
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____17135
                                                                    =
                                                                    let uu____17143
                                                                    =
                                                                    let uu____17144
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17145
                                                                    =
                                                                    let uu____17156
                                                                    =
                                                                    let uu____17157
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17157
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____17159
                                                                    =
                                                                    let uu____17160
                                                                    =
                                                                    let uu____17165
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____17165)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____17160
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____17156,
                                                                    uu____17159)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17144
                                                                    uu____17145
                                                                     in
                                                                    (uu____17143,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17135
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____17182 ->
                                                         ((let uu____17184 =
                                                             let uu____17190
                                                               =
                                                               let uu____17192
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____17194
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____17192
                                                                 uu____17194
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____17190)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____17184);
                                                          ([], [])))
                                                 in
                                              let uu____17202 =
                                                encode_elim ()  in
                                              (match uu____17202 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____17228 =
                                                       let uu____17231 =
                                                         let uu____17234 =
                                                           let uu____17237 =
                                                             let uu____17240
                                                               =
                                                               let uu____17243
                                                                 =
                                                                 let uu____17246
                                                                   =
                                                                   let uu____17247
                                                                    =
                                                                    let uu____17259
                                                                    =
                                                                    let uu____17260
                                                                    =
                                                                    let uu____17262
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____17262
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____17260
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____17259)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____17247
                                                                    in
                                                                 [uu____17246]
                                                                  in
                                                               FStar_List.append
                                                                 uu____17243
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____17240
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____17273 =
                                                             let uu____17276
                                                               =
                                                               let uu____17279
                                                                 =
                                                                 let uu____17282
                                                                   =
                                                                   let uu____17285
                                                                    =
                                                                    let uu____17288
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____17293
                                                                    =
                                                                    let uu____17296
                                                                    =
                                                                    let uu____17297
                                                                    =
                                                                    let uu____17305
                                                                    =
                                                                    let uu____17306
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17307
                                                                    =
                                                                    let uu____17318
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____17318)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17306
                                                                    uu____17307
                                                                     in
                                                                    (uu____17305,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17297
                                                                     in
                                                                    let uu____17331
                                                                    =
                                                                    let uu____17334
                                                                    =
                                                                    let uu____17335
                                                                    =
                                                                    let uu____17343
                                                                    =
                                                                    let uu____17344
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____17345
                                                                    =
                                                                    let uu____17356
                                                                    =
                                                                    let uu____17357
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____17357
                                                                    vars'  in
                                                                    let uu____17359
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____17356,
                                                                    uu____17359)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____17344
                                                                    uu____17345
                                                                     in
                                                                    (uu____17343,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____17335
                                                                     in
                                                                    [uu____17334]
                                                                     in
                                                                    uu____17296
                                                                    ::
                                                                    uu____17331
                                                                     in
                                                                    uu____17288
                                                                    ::
                                                                    uu____17293
                                                                     in
                                                                   FStar_List.append
                                                                    uu____17285
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____17282
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____17279
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____17276
                                                              in
                                                           FStar_List.append
                                                             uu____17237
                                                             uu____17273
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____17234
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____17231
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____17228
                                                      in
                                                   let uu____17376 =
                                                     let uu____17377 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____17377 g
                                                      in
                                                   (uu____17376, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____17411  ->
              fun se  ->
                match uu____17411 with
                | (g,env1) ->
                    let uu____17431 = encode_sigelt env1 se  in
                    (match uu____17431 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____17499 =
        match uu____17499 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____17536 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort  in
                 ((let uu____17544 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____17544
                   then
                     let uu____17549 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____17551 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____17553 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____17549 uu____17551 uu____17553
                   else ());
                  (let uu____17558 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____17558 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____17576 =
                         let uu____17584 =
                           let uu____17586 =
                             let uu____17588 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.op_Hat uu____17588
                               (Prims.op_Hat "_" (Prims.string_of_int i))
                              in
                           Prims.op_Hat "x_" uu____17586  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____17584
                          in
                       (match uu____17576 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____17608 = FStar_Options.log_queries ()
                                 in
                              if uu____17608
                              then
                                let uu____17611 =
                                  let uu____17613 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____17615 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____17617 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____17613 uu____17615 uu____17617
                                   in
                                FStar_Pervasives_Native.Some uu____17611
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____17633 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____17643 =
                                let uu____17646 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____17646  in
                              FStar_List.append uu____17633 uu____17643  in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____17658,t)) ->
                 let t_norm = norm_before_encoding env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____17678 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____17678 with
                  | (g,env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env')))
         in
      let uu____17699 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env)
         in
      match uu____17699 with | (uu____17726,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____17779  ->
              match uu____17779 with
              | (l,uu____17788,uu____17789) ->
                  let uu____17792 =
                    let uu____17804 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____17804, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____17792))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____17837  ->
              match uu____17837 with
              | (l,uu____17848,uu____17849) ->
                  let uu____17852 =
                    let uu____17853 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun uu____17856  ->
                         FStar_SMTEncoding_Term.Echo uu____17856) uu____17853
                     in
                  let uu____17857 =
                    let uu____17860 =
                      let uu____17861 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____17861  in
                    [uu____17860]  in
                  uu____17852 :: uu____17857))
       in
    (prefix, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____17879 =
      let uu____17882 =
        let uu____17883 = FStar_Util.psmap_empty ()  in
        let uu____17898 =
          let uu____17907 = FStar_Util.psmap_empty ()  in (uu____17907, [])
           in
        let uu____17914 =
          let uu____17916 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____17916 FStar_Ident.string_of_lid  in
        let uu____17918 = FStar_Util.smap_create (Prims.of_int (100))  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____17883;
          FStar_SMTEncoding_Env.fvar_bindings = uu____17898;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____17914;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____17918
        }  in
      [uu____17882]  in
    FStar_ST.op_Colon_Equals last_env uu____17879
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____17962 = FStar_ST.op_Bang last_env  in
      match uu____17962 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17990 ->
          let uu___1577_17993 = e  in
          let uu____17994 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1577_17993.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1577_17993.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1577_17993.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1577_17993.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1577_17993.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1577_17993.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1577_17993.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____17994;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1577_17993.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1577_17993.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____18002 = FStar_ST.op_Bang last_env  in
    match uu____18002 with
    | [] -> failwith "Empty env stack"
    | uu____18029::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
  
let (push_env : unit -> unit) =
  fun uu____18061  ->
    let uu____18062 = FStar_ST.op_Bang last_env  in
    match uu____18062 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd  in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
  
let (pop_env : unit -> unit) =
  fun uu____18122  ->
    let uu____18123 = FStar_ST.op_Bang last_env  in
    match uu____18123 with
    | [] -> failwith "Popping an empty stack"
    | uu____18150::tl -> FStar_ST.op_Colon_Equals last_env tl
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____18187  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____18240  ->
         let uu____18241 = snapshot_env ()  in
         match uu____18241 with
         | (env_depth,()) ->
             let uu____18263 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____18263 with
              | (varops_depth,()) ->
                  let uu____18285 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____18285 with
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
        (fun uu____18343  ->
           let uu____18344 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____18344 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____18439 = snapshot msg  in () 
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
        | (uu____18485::uu____18486,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1638_18494 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1638_18494.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1638_18494.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1638_18494.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____18495 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___1644_18522 = elt  in
        let uu____18523 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1644_18522.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1644_18522.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____18523;
          FStar_SMTEncoding_Term.a_names =
            (uu___1644_18522.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____18543 =
        let uu____18546 =
          let uu____18547 =
            let uu____18548 = FStar_Ident.ns_of_lid lid  in
            FStar_Ident.lid_of_ids uu____18548  in
          FStar_SMTEncoding_Term.Namespace uu____18547  in
        let uu____18549 = open_fact_db_tags env  in uu____18546 ::
          uu____18549
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____18543
  
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
      let uu____18576 = encode_sigelt env se  in
      match uu____18576 with
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
                (let uu____18622 =
                   let uu____18625 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____18625
                    in
                 match uu____18622 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____18640 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____18640
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____18670 = FStar_Options.log_queries ()  in
        if uu____18670
        then
          let uu____18675 =
            let uu____18676 =
              let uu____18678 =
                let uu____18680 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____18680 (FStar_String.concat ", ")
                 in
              Prims.op_Hat "encoding sigelt " uu____18678  in
            FStar_SMTEncoding_Term.Caption uu____18676  in
          uu____18675 :: decls
        else decls  in
      (let uu____18699 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____18699
       then
         let uu____18702 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____18702
       else ());
      (let env =
         let uu____18708 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____18708 tcenv  in
       let uu____18709 = encode_top_level_facts env se  in
       match uu____18709 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____18723 =
               let uu____18726 =
                 let uu____18729 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____18729
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____18726  in
             FStar_SMTEncoding_Z3.giveZ3 uu____18723)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____18762 = FStar_Options.log_queries ()  in
          if uu____18762
          then
            let msg = Prims.op_Hat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___1682_18782 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1682_18782.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1682_18782.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1682_18782.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1682_18782.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1682_18782.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1682_18782.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1682_18782.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1682_18782.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1682_18782.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1682_18782.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____18787 =
             let uu____18790 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____18790
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____18787  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____18810 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____18810
      then ([], [])
      else
        (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh ();
         (let name =
            let uu____18826 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_Util.format2 "%s %s"
              (if modul.FStar_Syntax_Syntax.is_interface
               then "interface"
               else "module") uu____18826
             in
          (let uu____18836 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____18836
           then
             let uu____18839 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____18839
           else ());
          (let env =
             let uu____18847 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____18847
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____18886  ->
                     fun se  ->
                       match uu____18886 with
                       | (g,env2) ->
                           let uu____18906 = encode_top_level_facts env2 se
                              in
                           (match uu____18906 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____18929 =
             encode_signature
               (let uu___1705_18938 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___1705_18938.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___1705_18938.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___1705_18938.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___1705_18938.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___1705_18938.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___1705_18938.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___1705_18938.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___1705_18938.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___1705_18938.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___1705_18938.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____18929 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____18954 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____18954
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____18960 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____18960))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun tcmod  ->
      fun uu____18988  ->
        match uu____18988 with
        | (decls,fvbs) ->
            let uu____19001 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
            if uu____19001
            then ()
            else
              (let name =
                 let uu____19008 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name
                    in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu____19008
                  in
               (let uu____19018 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____19018
                then
                  let uu____19021 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int
                     in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____19021
                else ());
               (let env =
                  let uu____19029 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv  in
                  FStar_All.pipe_right uu____19029
                    FStar_SMTEncoding_Env.reset_current_module_fvbs
                   in
                let env1 =
                  let uu____19031 = FStar_All.pipe_right fvbs FStar_List.rev
                     in
                  FStar_All.pipe_right uu____19031
                    (FStar_List.fold_left
                       (fun env1  ->
                          fun fvb  ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env)
                   in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____19045 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____19045
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
        (let uu____19107 =
           let uu____19109 = FStar_TypeChecker_Env.current_module tcenv  in
           FStar_Ident.string_of_lid uu____19109  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____19107);
        (let env =
           let uu____19111 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____19111 tcenv  in
         let uu____19112 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____19149 = aux rest  in
                 (match uu____19149 with
                  | (out,rest1) ->
                      let t =
                        let uu____19177 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____19177 with
                        | FStar_Pervasives_Native.Some uu____19180 ->
                            let uu____19181 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____19181
                              x.FStar_Syntax_Syntax.sort
                        | uu____19182 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        norm_with_steps
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____19186 =
                        let uu____19189 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___1748_19192 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1748_19192.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1748_19192.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____19189 :: out  in
                      (uu____19186, rest1))
             | uu____19197 -> ([], bindings)  in
           let uu____19204 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____19204 with
           | (closing,bindings) ->
               let uu____19229 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____19229, bindings)
            in
         match uu____19112 with
         | (q1,bindings) ->
             let uu____19252 = encode_env_bindings env bindings  in
             (match uu____19252 with
              | (env_decls,env1) ->
                  ((let uu____19274 =
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
                    if uu____19274
                    then
                      let uu____19281 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula {: %s\n"
                        uu____19281
                    else ());
                   (let uu____19286 =
                      FStar_Util.record_time
                        (fun uu____19301  ->
                           FStar_SMTEncoding_EncodeTerm.encode_formula q1
                             env1)
                       in
                    match uu____19286 with
                    | ((phi,qdecls),ms) ->
                        let uu____19325 =
                          let uu____19330 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____19330 phi
                           in
                        (match uu____19325 with
                         | (labels,phi1) ->
                             let uu____19347 = encode_labels labels  in
                             (match uu____19347 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____19383 =
                                      FStar_Options.log_queries ()  in
                                    if uu____19383
                                    then
                                      let uu____19388 =
                                        let uu____19389 =
                                          let uu____19391 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.op_Hat
                                            "Encoding query formula : "
                                            uu____19391
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____19389
                                         in
                                      [uu____19388]
                                    else []  in
                                  let query_prelude =
                                    let uu____19399 =
                                      let uu____19400 =
                                        let uu____19401 =
                                          let uu____19404 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____19411 =
                                            let uu____19414 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____19414
                                             in
                                          FStar_List.append uu____19404
                                            uu____19411
                                           in
                                        FStar_List.append env_decls
                                          uu____19401
                                         in
                                      FStar_All.pipe_right uu____19400
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____19399
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____19424 =
                                      let uu____19432 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____19433 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____19432,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____19433)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____19424
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  ((let uu____19446 =
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
                                    if uu____19446
                                    then
                                      FStar_Util.print_string
                                        "} Done encoding\n"
                                    else ());
                                   (let uu____19457 =
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
                                    if uu____19457
                                    then
                                      FStar_Util.print1
                                        "Encoding took %sms\n"
                                        (Prims.string_of_int ms)
                                    else ());
                                   (query_prelude, labels, qry, suffix))))))))
  