open Prims
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | { mk = mk1; is;_} -> mk1 
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  -> match projectee with | { mk = mk1; is;_} -> is 
let (prims : prims_t) =
  let uu____119 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____119 with
  | (asym,a) ->
      let uu____126 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____126 with
       | (xsym,x) ->
           let uu____133 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____133 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____194 =
                      let uu____205 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____205, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____194  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____227 =
                      let uu____234 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____234)  in
                    FStar_SMTEncoding_Util.mkApp uu____227  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____247 =
                    let uu____250 =
                      let uu____253 =
                        let uu____256 =
                          let uu____257 =
                            let uu____264 =
                              let uu____265 =
                                let uu____276 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____276)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____265
                               in
                            (uu____264, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____257  in
                        let uu____285 =
                          let uu____288 =
                            let uu____289 =
                              let uu____296 =
                                let uu____297 =
                                  let uu____308 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____308)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____297
                                 in
                              (uu____296,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____289  in
                          [uu____288]  in
                        uu____256 :: uu____285  in
                      xtok_decl :: uu____253  in
                    xname_decl :: uu____250  in
                  (xtok1, (FStar_List.length vars), uu____247)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____401 =
                    let uu____420 =
                      let uu____437 =
                        let uu____438 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____438
                         in
                      quant axy uu____437  in
                    (FStar_Parser_Const.op_Eq, uu____420)  in
                  let uu____453 =
                    let uu____474 =
                      let uu____493 =
                        let uu____510 =
                          let uu____511 =
                            let uu____512 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____512  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____511
                           in
                        quant axy uu____510  in
                      (FStar_Parser_Const.op_notEq, uu____493)  in
                    let uu____527 =
                      let uu____548 =
                        let uu____567 =
                          let uu____584 =
                            let uu____585 =
                              let uu____586 =
                                let uu____591 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____592 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____591, uu____592)  in
                              FStar_SMTEncoding_Util.mkLT uu____586  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____585
                             in
                          quant xy uu____584  in
                        (FStar_Parser_Const.op_LT, uu____567)  in
                      let uu____607 =
                        let uu____628 =
                          let uu____647 =
                            let uu____664 =
                              let uu____665 =
                                let uu____666 =
                                  let uu____671 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____672 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____671, uu____672)  in
                                FStar_SMTEncoding_Util.mkLTE uu____666  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____665
                               in
                            quant xy uu____664  in
                          (FStar_Parser_Const.op_LTE, uu____647)  in
                        let uu____687 =
                          let uu____708 =
                            let uu____727 =
                              let uu____744 =
                                let uu____745 =
                                  let uu____746 =
                                    let uu____751 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____752 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____751, uu____752)  in
                                  FStar_SMTEncoding_Util.mkGT uu____746  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____745
                                 in
                              quant xy uu____744  in
                            (FStar_Parser_Const.op_GT, uu____727)  in
                          let uu____767 =
                            let uu____788 =
                              let uu____807 =
                                let uu____824 =
                                  let uu____825 =
                                    let uu____826 =
                                      let uu____831 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____832 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____831, uu____832)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____826
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____825
                                   in
                                quant xy uu____824  in
                              (FStar_Parser_Const.op_GTE, uu____807)  in
                            let uu____847 =
                              let uu____868 =
                                let uu____887 =
                                  let uu____904 =
                                    let uu____905 =
                                      let uu____906 =
                                        let uu____911 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____912 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____911, uu____912)  in
                                      FStar_SMTEncoding_Util.mkSub uu____906
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____905
                                     in
                                  quant xy uu____904  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____887)
                                 in
                              let uu____927 =
                                let uu____948 =
                                  let uu____967 =
                                    let uu____984 =
                                      let uu____985 =
                                        let uu____986 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____986
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____985
                                       in
                                    quant qx uu____984  in
                                  (FStar_Parser_Const.op_Minus, uu____967)
                                   in
                                let uu____1001 =
                                  let uu____1022 =
                                    let uu____1041 =
                                      let uu____1058 =
                                        let uu____1059 =
                                          let uu____1060 =
                                            let uu____1065 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1066 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1065, uu____1066)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1060
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1059
                                         in
                                      quant xy uu____1058  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1041)
                                     in
                                  let uu____1081 =
                                    let uu____1102 =
                                      let uu____1121 =
                                        let uu____1138 =
                                          let uu____1139 =
                                            let uu____1140 =
                                              let uu____1145 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1146 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1145, uu____1146)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1140
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1139
                                           in
                                        quant xy uu____1138  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1121)
                                       in
                                    let uu____1161 =
                                      let uu____1182 =
                                        let uu____1201 =
                                          let uu____1218 =
                                            let uu____1219 =
                                              let uu____1220 =
                                                let uu____1225 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1226 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1225, uu____1226)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1220
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1219
                                             in
                                          quant xy uu____1218  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1201)
                                         in
                                      let uu____1241 =
                                        let uu____1262 =
                                          let uu____1281 =
                                            let uu____1298 =
                                              let uu____1299 =
                                                let uu____1300 =
                                                  let uu____1305 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1306 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1305, uu____1306)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1300
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1299
                                               in
                                            quant xy uu____1298  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1281)
                                           in
                                        let uu____1321 =
                                          let uu____1342 =
                                            let uu____1361 =
                                              let uu____1378 =
                                                let uu____1379 =
                                                  let uu____1380 =
                                                    let uu____1385 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1386 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1385, uu____1386)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1380
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1379
                                                 in
                                              quant xy uu____1378  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1361)
                                             in
                                          let uu____1401 =
                                            let uu____1422 =
                                              let uu____1441 =
                                                let uu____1458 =
                                                  let uu____1459 =
                                                    let uu____1460 =
                                                      let uu____1465 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1466 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1465,
                                                        uu____1466)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1460
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1459
                                                   in
                                                quant xy uu____1458  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1441)
                                               in
                                            let uu____1481 =
                                              let uu____1502 =
                                                let uu____1521 =
                                                  let uu____1538 =
                                                    let uu____1539 =
                                                      let uu____1540 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1540
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1539
                                                     in
                                                  quant qx uu____1538  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1521)
                                                 in
                                              [uu____1502]  in
                                            uu____1422 :: uu____1481  in
                                          uu____1342 :: uu____1401  in
                                        uu____1262 :: uu____1321  in
                                      uu____1182 :: uu____1241  in
                                    uu____1102 :: uu____1161  in
                                  uu____1022 :: uu____1081  in
                                uu____948 :: uu____1001  in
                              uu____868 :: uu____927  in
                            uu____788 :: uu____847  in
                          uu____708 :: uu____767  in
                        uu____628 :: uu____687  in
                      uu____548 :: uu____607  in
                    uu____474 :: uu____527  in
                  uu____401 :: uu____453  in
                let mk1 l v1 =
                  let uu____1862 =
                    let uu____1873 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1955  ->
                              match uu____1955 with
                              | (l',uu____1973) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____1873
                      (FStar_Option.map
                         (fun uu____2062  ->
                            match uu____2062 with
                            | (uu____2087,b) ->
                                let uu____2117 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2117 v1))
                     in
                  FStar_All.pipe_right uu____1862 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2191  ->
                          match uu____2191 with
                          | (l',uu____2209) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string,FStar_SMTEncoding_Term.sort)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_SMTEncoding_Term.decl)
  =
  fun rng  ->
    fun env  ->
      fun tapp  ->
        fun vars  ->
          let uu____2270 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2270 with
          | (xxsym,xx) ->
              let uu____2277 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2277 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2287 =
                     let uu____2294 =
                       let uu____2295 =
                         let uu____2306 =
                           let uu____2307 =
                             let uu____2312 =
                               let uu____2313 =
                                 let uu____2318 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2318)  in
                               FStar_SMTEncoding_Util.mkEq uu____2313  in
                             (xx_has_type, uu____2312)  in
                           FStar_SMTEncoding_Util.mkImp uu____2307  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2306)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2295  in
                     let uu____2337 =
                       let uu____2338 =
                         let uu____2339 =
                           let uu____2340 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2340  in
                         Prims.strcat module_name uu____2339  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2338
                        in
                     (uu____2294, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2337)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2287)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____2388 =
      let uu____2389 =
        let uu____2396 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2396, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2389  in
    let uu____2397 =
      let uu____2400 =
        let uu____2401 =
          let uu____2408 =
            let uu____2409 =
              let uu____2420 =
                let uu____2421 =
                  let uu____2426 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2426)  in
                FStar_SMTEncoding_Util.mkImp uu____2421  in
              ([[typing_pred]], [xx], uu____2420)  in
            let uu____2443 =
              let uu____2458 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2458  in
            uu____2443 uu____2409  in
          (uu____2408, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2401  in
      [uu____2400]  in
    uu____2388 :: uu____2397  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2482 =
      let uu____2483 =
        let uu____2490 =
          let uu____2491 = FStar_TypeChecker_Env.get_range env  in
          let uu____2492 =
            let uu____2503 =
              let uu____2508 =
                let uu____2511 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2511]  in
              [uu____2508]  in
            let uu____2516 =
              let uu____2517 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2517 tt  in
            (uu____2503, [bb], uu____2516)  in
          FStar_SMTEncoding_Term.mkForall uu____2491 uu____2492  in
        (uu____2490, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2483  in
    let uu____2530 =
      let uu____2533 =
        let uu____2534 =
          let uu____2541 =
            let uu____2542 =
              let uu____2553 =
                let uu____2554 =
                  let uu____2559 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2559)  in
                FStar_SMTEncoding_Util.mkImp uu____2554  in
              ([[typing_pred]], [xx], uu____2553)  in
            let uu____2576 =
              let uu____2591 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2591  in
            uu____2576 uu____2542  in
          (uu____2541, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2534  in
      [uu____2533]  in
    uu____2482 :: uu____2530  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____2609 =
        let uu____2614 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____2614, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____2609  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____2630 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2630  in
    let uu____2633 =
      let uu____2634 =
        let uu____2641 =
          let uu____2642 = FStar_TypeChecker_Env.get_range env  in
          let uu____2643 =
            let uu____2654 =
              let uu____2659 =
                let uu____2662 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2662]  in
              [uu____2659]  in
            let uu____2667 =
              let uu____2668 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2668 tt  in
            (uu____2654, [bb], uu____2667)  in
          FStar_SMTEncoding_Term.mkForall uu____2642 uu____2643  in
        (uu____2641, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2634  in
    let uu____2681 =
      let uu____2684 =
        let uu____2685 =
          let uu____2692 =
            let uu____2693 =
              let uu____2704 =
                let uu____2705 =
                  let uu____2710 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2710)  in
                FStar_SMTEncoding_Util.mkImp uu____2705  in
              ([[typing_pred]], [xx], uu____2704)  in
            let uu____2727 =
              let uu____2742 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2742  in
            uu____2727 uu____2693  in
          (uu____2692, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2685  in
      let uu____2743 =
        let uu____2746 =
          let uu____2747 =
            let uu____2754 =
              let uu____2755 =
                let uu____2766 =
                  let uu____2767 =
                    let uu____2772 =
                      let uu____2773 =
                        let uu____2776 =
                          let uu____2779 =
                            let uu____2782 =
                              let uu____2783 =
                                let uu____2788 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2789 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2788, uu____2789)  in
                              FStar_SMTEncoding_Util.mkGT uu____2783  in
                            let uu____2790 =
                              let uu____2793 =
                                let uu____2794 =
                                  let uu____2799 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2800 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2799, uu____2800)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2794  in
                              let uu____2801 =
                                let uu____2804 =
                                  let uu____2805 =
                                    let uu____2810 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2811 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2810, uu____2811)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2805  in
                                [uu____2804]  in
                              uu____2793 :: uu____2801  in
                            uu____2782 :: uu____2790  in
                          typing_pred_y :: uu____2779  in
                        typing_pred :: uu____2776  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2773  in
                    (uu____2772, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2767  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2766)
                 in
              let uu____2832 =
                let uu____2847 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2847  in
              uu____2832 uu____2755  in
            (uu____2754,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2747  in
        [uu____2746]  in
      uu____2684 :: uu____2743  in
    uu____2633 :: uu____2681  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2871 =
      let uu____2872 =
        let uu____2879 =
          let uu____2880 = FStar_TypeChecker_Env.get_range env  in
          let uu____2881 =
            let uu____2892 =
              let uu____2897 =
                let uu____2900 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2900]  in
              [uu____2897]  in
            let uu____2905 =
              let uu____2906 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2906 tt  in
            (uu____2892, [bb], uu____2905)  in
          FStar_SMTEncoding_Term.mkForall uu____2880 uu____2881  in
        (uu____2879, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2872  in
    let uu____2919 =
      let uu____2922 =
        let uu____2923 =
          let uu____2930 =
            let uu____2931 =
              let uu____2942 =
                let uu____2943 =
                  let uu____2948 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____2948)  in
                FStar_SMTEncoding_Util.mkImp uu____2943  in
              ([[typing_pred]], [xx], uu____2942)  in
            let uu____2965 =
              let uu____2980 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2980  in
            uu____2965 uu____2931  in
          (uu____2930, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2923  in
      [uu____2922]  in
    uu____2871 :: uu____2919  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3000 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3000]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3020 =
      let uu____3021 =
        let uu____3028 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3028, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3021  in
    [uu____3020]  in
  let mk_and_interp env conj uu____3044 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3069 =
      let uu____3070 =
        let uu____3077 =
          let uu____3078 = FStar_TypeChecker_Env.get_range env  in
          let uu____3079 =
            let uu____3090 =
              let uu____3091 =
                let uu____3096 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3096, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3091  in
            ([[l_and_a_b]], [aa; bb], uu____3090)  in
          FStar_SMTEncoding_Term.mkForall uu____3078 uu____3079  in
        (uu____3077, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3070  in
    [uu____3069]  in
  let mk_or_interp env disj uu____3132 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3157 =
      let uu____3158 =
        let uu____3165 =
          let uu____3166 = FStar_TypeChecker_Env.get_range env  in
          let uu____3167 =
            let uu____3178 =
              let uu____3179 =
                let uu____3184 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3184, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3179  in
            ([[l_or_a_b]], [aa; bb], uu____3178)  in
          FStar_SMTEncoding_Term.mkForall uu____3166 uu____3167  in
        (uu____3165, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3158  in
    [uu____3157]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3245 =
      let uu____3246 =
        let uu____3253 =
          let uu____3254 = FStar_TypeChecker_Env.get_range env  in
          let uu____3255 =
            let uu____3266 =
              let uu____3267 =
                let uu____3272 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3272, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3267  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3266)  in
          FStar_SMTEncoding_Term.mkForall uu____3254 uu____3255  in
        (uu____3253, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3246  in
    [uu____3245]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____3343 =
      let uu____3344 =
        let uu____3351 =
          let uu____3352 = FStar_TypeChecker_Env.get_range env  in
          let uu____3353 =
            let uu____3364 =
              let uu____3365 =
                let uu____3370 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3370, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3365  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3364)  in
          FStar_SMTEncoding_Term.mkForall uu____3352 uu____3353  in
        (uu____3351, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3344  in
    [uu____3343]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3439 =
      let uu____3440 =
        let uu____3447 =
          let uu____3448 = FStar_TypeChecker_Env.get_range env  in
          let uu____3449 =
            let uu____3460 =
              let uu____3461 =
                let uu____3466 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3466, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3461  in
            ([[l_imp_a_b]], [aa; bb], uu____3460)  in
          FStar_SMTEncoding_Term.mkForall uu____3448 uu____3449  in
        (uu____3447, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3440  in
    [uu____3439]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3527 =
      let uu____3528 =
        let uu____3535 =
          let uu____3536 = FStar_TypeChecker_Env.get_range env  in
          let uu____3537 =
            let uu____3548 =
              let uu____3549 =
                let uu____3554 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3554, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3549  in
            ([[l_iff_a_b]], [aa; bb], uu____3548)  in
          FStar_SMTEncoding_Term.mkForall uu____3536 uu____3537  in
        (uu____3535, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3528  in
    [uu____3527]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3604 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3604  in
    let uu____3607 =
      let uu____3608 =
        let uu____3615 =
          let uu____3616 = FStar_TypeChecker_Env.get_range env  in
          let uu____3617 =
            let uu____3628 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3628)  in
          FStar_SMTEncoding_Term.mkForall uu____3616 uu____3617  in
        (uu____3615, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3608  in
    [uu____3607]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3664 =
      let uu____3665 =
        let uu____3672 =
          let uu____3673 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3673 range_ty  in
        let uu____3674 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3672, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3674)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3665  in
    [uu____3664]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____3712 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3712 x1 t  in
      let uu____3713 = FStar_TypeChecker_Env.get_range env  in
      let uu____3714 =
        let uu____3725 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3725)  in
      FStar_SMTEncoding_Term.mkForall uu____3713 uu____3714  in
    let uu____3742 =
      let uu____3743 =
        let uu____3750 =
          let uu____3751 = FStar_TypeChecker_Env.get_range env  in
          let uu____3752 =
            let uu____3763 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3763)  in
          FStar_SMTEncoding_Term.mkForall uu____3751 uu____3752  in
        (uu____3750,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3743  in
    [uu____3742]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3811 =
      let uu____3812 =
        let uu____3819 =
          let uu____3820 = FStar_TypeChecker_Env.get_range env  in
          let uu____3821 =
            let uu____3836 =
              let uu____3837 =
                let uu____3842 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3843 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3842, uu____3843)  in
              FStar_SMTEncoding_Util.mkAnd uu____3837  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3836)
             in
          FStar_SMTEncoding_Term.mkForall' uu____3820 uu____3821  in
        (uu____3819,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3812  in
    [uu____3811]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
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
          let uu____4319 =
            FStar_Util.find_opt
              (fun uu____4355  ->
                 match uu____4355 with
                 | (l,uu____4369) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4319 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4409,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4466 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4466 with
        | (form,decls) ->
            let uu____4475 =
              let uu____4478 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____4478]  in
            FStar_List.append decls uu____4475
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____4528 =
                ((let uu____4531 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4531) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4528
              then
                let arg_sorts =
                  let uu____4541 =
                    let uu____4542 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4542.FStar_Syntax_Syntax.n  in
                  match uu____4541 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4548) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4586  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4593 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4595 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4595 with
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
                    ([d; dd], env1)
              else
                (let uu____4624 = prims.is lid  in
                 if uu____4624
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4632 = prims.mk lid vname  in
                   match uu____4632 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4659 =
                      let uu____4678 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4678 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4706 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4706
                            then
                              let uu____4709 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___383_4712 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___383_4712.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___383_4712.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___383_4712.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___383_4712.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___383_4712.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___383_4712.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___383_4712.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___383_4712.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___383_4712.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___383_4712.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___383_4712.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___383_4712.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___383_4712.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___383_4712.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___383_4712.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___383_4712.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___383_4712.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___383_4712.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___383_4712.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___383_4712.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___383_4712.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___383_4712.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___383_4712.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___383_4712.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___383_4712.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___383_4712.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___383_4712.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___383_4712.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___383_4712.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___383_4712.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___383_4712.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___383_4712.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___383_4712.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___383_4712.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___383_4712.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___383_4712.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___383_4712.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___383_4712.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___383_4712.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___383_4712.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___383_4712.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___383_4712.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4709
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4732 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4732)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4659 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4812 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4812 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4839 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___373_4897  ->
                                       match uu___373_4897 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4901 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4901 with
                                            | (uu____4922,(xxsym,uu____4924))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4942 =
                                                  let uu____4943 =
                                                    let uu____4950 =
                                                      let uu____4951 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4952 =
                                                        let uu____4963 =
                                                          let uu____4964 =
                                                            let uu____4969 =
                                                              let uu____4970
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4970
                                                               in
                                                            (vapp,
                                                              uu____4969)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4964
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4963)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4951 uu____4952
                                                       in
                                                    (uu____4950,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4943
                                                   in
                                                [uu____4942])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4981 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4981 with
                                            | (uu____5002,(xxsym,uu____5004))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
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
                                                let uu____5027 =
                                                  let uu____5028 =
                                                    let uu____5035 =
                                                      let uu____5036 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5037 =
                                                        let uu____5048 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5048)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5036 uu____5037
                                                       in
                                                    (uu____5035,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5028
                                                   in
                                                [uu____5027])
                                       | uu____5057 -> []))
                                in
                             let uu____5058 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5058 with
                              | (vars,guards,env',decls1,uu____5085) ->
                                  let uu____5098 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5111 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5111, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5115 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5115 with
                                         | (g,ds) ->
                                             let uu____5128 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5128,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5098 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5145 =
                                           let uu____5152 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5152)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5145
                                          in
                                       let uu____5157 =
                                         let vname_decl =
                                           let uu____5165 =
                                             let uu____5176 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5196  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5176,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5165
                                            in
                                         let uu____5205 =
                                           let env2 =
                                             let uu___384_5211 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___384_5211.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____5212 =
                                             let uu____5213 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5213  in
                                           if uu____5212
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5205 with
                                         | (tok_typing,decls2) ->
                                             let uu____5227 =
                                               match formals with
                                               | [] ->
                                                   let tok_typing1 =
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname))
                                                      in
                                                   let uu____5247 =
                                                     let uu____5248 =
                                                       let uu____5251 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____5251
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____5248
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____5247)
                                               | uu____5260 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____5273 =
                                                       let uu____5280 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____5280]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____5273
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____5299 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____5300 =
                                                       let uu____5311 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____5311)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____5299 uu____5300
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5321 =
                                                       let uu____5328 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____5328,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5321
                                                      in
                                                   let tok_typing1 =
                                                     let ff =
                                                       ("ty",
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     let f =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         ff
                                                        in
                                                     let vtok_app_l =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         vtok_tm [ff]
                                                        in
                                                     let vtok_app_r =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         f
                                                         [(vtok,
                                                            FStar_SMTEncoding_Term.Term_sort)]
                                                        in
                                                     let guarded_tok_typing =
                                                       let uu____5355 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5356 =
                                                         let uu____5367 =
                                                           let uu____5368 =
                                                             let uu____5373 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____5374 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____5373,
                                                               uu____5374)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____5368
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____5367)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5355
                                                         uu____5356
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (guarded_tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname))
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____5227 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5157 with
                                        | (decls2,env2) ->
                                            let uu____5419 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5429 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5429 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5444 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5444,
                                                    decls)
                                               in
                                            (match uu____5419 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5461 =
                                                     let uu____5468 =
                                                       let uu____5469 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5470 =
                                                         let uu____5481 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5481)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5469
                                                         uu____5470
                                                        in
                                                     (uu____5468,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5461
                                                    in
                                                 let freshness =
                                                   let uu____5493 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5493
                                                   then
                                                     let uu____5498 =
                                                       let uu____5499 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5500 =
                                                         let uu____5511 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5526 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5511,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5526)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5499
                                                         uu____5500
                                                        in
                                                     let uu____5529 =
                                                       let uu____5532 =
                                                         let uu____5533 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5533 env2
                                                           vapp vars
                                                          in
                                                       [uu____5532]  in
                                                     uu____5498 :: uu____5529
                                                   else []  in
                                                 let g =
                                                   let uu____5538 =
                                                     let uu____5541 =
                                                       let uu____5544 =
                                                         let uu____5547 =
                                                           let uu____5550 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5550
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5547
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5544
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5541
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5538
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5587 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5587 with
          | FStar_Pervasives_Native.None  ->
              let t_norm1 =
                let uu____5601 =
                  FStar_Syntax_Util.arrow_formals_comp_aux false false t_norm
                   in
                match uu____5601 with
                | (bs,c) ->
                    if (FStar_List.length bs) = (Prims.parse_int "0")
                    then t_norm
                    else FStar_Syntax_Util.arrow bs c
                 in
              let uu____5643 = encode_free_var false env x t t_norm1 []  in
              (match uu____5643 with
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
            (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____5710 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5710 with
            | (decls,env1) ->
                let uu____5729 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5729
                then
                  let uu____5736 =
                    let uu____5739 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5739  in
                  (uu____5736, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____5797  ->
                fun lb  ->
                  match uu____5797 with
                  | (decls,env1) ->
                      let uu____5817 =
                        let uu____5824 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5824
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5817 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5847 = FStar_Syntax_Util.head_and_args t  in
    match uu____5847 with
    | (hd1,args) ->
        let uu____5890 =
          let uu____5891 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5891.FStar_Syntax_Syntax.n  in
        (match uu____5890 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5895,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5918 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5924 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___385_5930 = en  in
    let uu____5931 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___385_5930.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___385_5930.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___385_5930.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___385_5930.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___385_5930.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____5931;
      FStar_SMTEncoding_Env.nolabels =
        (uu___385_5930.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___385_5930.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___385_5930.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___385_5930.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___385_5930.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5961  ->
      fun quals  ->
        match uu____5961 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____6065 = FStar_Util.first_N nbinders formals  in
              match uu____6065 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6166  ->
                         fun uu____6167  ->
                           match (uu____6166, uu____6167) with
                           | ((formal,uu____6193),(binder,uu____6195)) ->
                               let uu____6216 =
                                 let uu____6223 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6223)  in
                               FStar_Syntax_Syntax.NT uu____6216) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6237 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6278  ->
                              match uu____6278 with
                              | (x,i) ->
                                  let uu____6297 =
                                    let uu___386_6298 = x  in
                                    let uu____6299 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_6298.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_6298.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6299
                                    }  in
                                  (uu____6297, i)))
                       in
                    FStar_All.pipe_right uu____6237
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6323 =
                      let uu____6328 = FStar_Syntax_Subst.compress body  in
                      let uu____6329 =
                        let uu____6330 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6330
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6328 uu____6329
                       in
                    uu____6323 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6413 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6413
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___387_6418 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___387_6418.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___387_6418.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___387_6418.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___387_6418.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___387_6418.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___387_6418.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___387_6418.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___387_6418.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___387_6418.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___387_6418.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___387_6418.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___387_6418.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___387_6418.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___387_6418.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___387_6418.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___387_6418.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___387_6418.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___387_6418.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___387_6418.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___387_6418.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___387_6418.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___387_6418.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___387_6418.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___387_6418.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___387_6418.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___387_6418.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___387_6418.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___387_6418.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___387_6418.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___387_6418.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___387_6418.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___387_6418.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___387_6418.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___387_6418.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___387_6418.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___387_6418.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___387_6418.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___387_6418.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___387_6418.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___387_6418.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___387_6418.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___387_6418.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6463 = FStar_Syntax_Util.abs_formals e  in
                match uu____6463 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6543::uu____6544 ->
                         let t_norm' =
                           let uu____6568 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           FStar_All.pipe_left FStar_Syntax_Util.unascribe
                             uu____6568
                            in
                         (match t_norm'.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_arrow uu____6603 ->
                              let uu____6618 =
                                FStar_Syntax_Util.arrow_formals_comp_aux
                                  false false t_norm1
                                 in
                              (match uu____6618 with
                               | (formals,c) ->
                                   ((let uu____6682 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug
                                            env.FStar_SMTEncoding_Env.tcenv)
                                         (FStar_Options.Other "SMTEncoding")
                                        in
                                     if uu____6682
                                     then
                                       let uu____6683 =
                                         FStar_Syntax_Print.term_to_string
                                           t_norm1
                                          in
                                       let uu____6684 =
                                         FStar_Syntax_Print.binders_to_string
                                           ", " formals
                                          in
                                       let uu____6685 =
                                         FStar_Syntax_Print.comp_to_string c
                                          in
                                       FStar_Util.print3
                                         "Destruct_bound_function_lid:\n\tt_norm=%s\n\tformals=%s\n\tc=%s\n"
                                         uu____6683 uu____6684 uu____6685
                                     else ());
                                    (let nformals = FStar_List.length formals
                                        in
                                     let nbinders = FStar_List.length binders
                                        in
                                     let tres = get_result_type c  in
                                     let uu____6704 =
                                       (nformals < nbinders) &&
                                         (FStar_Syntax_Util.is_total_comp c)
                                        in
                                     if uu____6704
                                     then
                                       let uu____6747 =
                                         FStar_Util.first_N nformals binders
                                          in
                                       match uu____6747 with
                                       | (bs0,rest) ->
                                           let c1 =
                                             let subst1 =
                                               FStar_List.map2
                                                 (fun uu____6867  ->
                                                    fun uu____6868  ->
                                                      match (uu____6867,
                                                              uu____6868)
                                                      with
                                                      | ((x,uu____6894),
                                                         (b,uu____6896)) ->
                                                          let uu____6917 =
                                                            let uu____6924 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            (x, uu____6924)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____6917)
                                                 formals bs0
                                                in
                                             FStar_Syntax_Subst.subst_comp
                                               subst1 c
                                              in
                                           let body1 =
                                             FStar_Syntax_Util.abs rest body
                                               lopt
                                              in
                                           let uu____6932 =
                                             let uu____6961 =
                                               get_result_type c1  in
                                             (bs0, body1, bs0, uu____6961)
                                              in
                                           (uu____6932, false)
                                     else
                                       if nformals > nbinders
                                       then
                                         (let uu____7055 =
                                            eta_expand1 binders formals body
                                              tres
                                             in
                                          match uu____7055 with
                                          | (binders1,body1) ->
                                              ((binders1, body1, formals,
                                                 tres), false))
                                       else
                                         ((binders, body, formals, tres),
                                           false))))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____7222) ->
                              let uu____7227 =
                                let uu____7256 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____7256  in
                              (uu____7227, true)
                          | uu____7345 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                  FStar_TypeChecker_Env.Beta;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF;
                                  FStar_TypeChecker_Env.Exclude
                                    FStar_TypeChecker_Env.Zeta;
                                  FStar_TypeChecker_Env.UnfoldUntil
                                    FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.EraseUniverses]
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____7347 ->
                              let uu____7348 =
                                let uu____7349 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____7350 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____7349 uu____7350
                                 in
                              failwith uu____7348)
                     | uu____7383 ->
                         let rec aux' t_norm2 =
                           let uu____7422 =
                             let uu____7423 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____7423.FStar_Syntax_Syntax.n  in
                           match uu____7422 with
                           | FStar_Syntax_Syntax.Tm_arrow uu____7458 ->
                               let uu____7473 =
                                 FStar_Syntax_Util.arrow_formals_comp_aux
                                   false false t_norm2
                                  in
                               (match uu____7473 with
                                | (formals,c) ->
                                    let tres = get_result_type c  in
                                    let uu____7539 =
                                      eta_expand1 [] formals e tres  in
                                    (match uu____7539 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7663) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7668 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___389_7737  ->
                  match () with
                  | () ->
                      let uu____7744 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____7744
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____7756 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____7819  ->
                                   fun lb  ->
                                     match uu____7819 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____7874 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____7874
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____7877 =
                                             let uu____7886 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____7886
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____7877 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____7756 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____8012 =
                                 if
                                   fvb.FStar_SMTEncoding_Env.smt_arity =
                                     (Prims.parse_int "0")
                                 then
                                   FStar_SMTEncoding_Util.mkFreeV
                                     ((fvb.FStar_SMTEncoding_Env.smt_id),
                                       FStar_SMTEncoding_Term.Term_sort)
                                 else
                                   FStar_SMTEncoding_EncodeTerm.raise_arity_mismatch
                                     fvb.FStar_SMTEncoding_Env.smt_id
                                     fvb.FStar_SMTEncoding_Env.smt_arity
                                     (Prims.parse_int "0") rng
                                  in
                               match vars with
                               | [] -> mk_fv ()
                               | uu____8018 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8026 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____8026 vars)
                                   else
                                     (let uu____8028 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____8028)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____8088;
                                    FStar_Syntax_Syntax.lbeff = uu____8089;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8091;
                                    FStar_Syntax_Syntax.lbpos = uu____8092;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8116 =
                                     let uu____8125 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8125 with
                                     | (tcenv',uu____8143,e_t) ->
                                         let uu____8149 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8166 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8149 with
                                          | (e1,t_norm1) ->
                                              ((let uu___390_8192 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___390_8192.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8116 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8206 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____8206 with
                                         | ((binders,body,uu____8227,t_body),curry)
                                             ->
                                             ((let uu____8239 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8239
                                               then
                                                 let uu____8240 =
                                                   let uu____8241 =
                                                     FStar_Syntax_Subst.compress
                                                       e1
                                                      in
                                                   FStar_Syntax_Print.tag_of_term
                                                     uu____8241
                                                    in
                                                 let uu____8242 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8243 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8244 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t_norm1
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let (def=%s) : binders=[%s], body=%s @ type t_norm=%s\n"
                                                   uu____8240 uu____8242
                                                   uu____8243 uu____8244
                                               else ());
                                              (let uu____8246 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8246 with
                                               | (vars,guards,env'1,binder_decls,uu____8273)
                                                   ->
                                                   let body1 =
                                                     let uu____8287 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8287
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else
                                                       FStar_Syntax_Util.ascribe
                                                         body
                                                         ((FStar_Util.Inl
                                                             t_body),
                                                           FStar_Pervasives_Native.None)
                                                      in
                                                   let app =
                                                     let uu____8308 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____8308 curry
                                                       fvb vars
                                                      in
                                                   let uu____8309 =
                                                     let is_logical =
                                                       let uu____8321 =
                                                         let uu____8322 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____8322.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____8321 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____8326 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____8328 =
                                                         let uu____8329 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____8329
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____8328
                                                         (fun lid  ->
                                                            let uu____8337 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____8337
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____8338 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____8338
                                                     then
                                                       let uu____8351 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____8352 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____8351,
                                                         uu____8352)
                                                     else
                                                       (let uu____8362 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____8362))
                                                      in
                                                   (match uu____8309 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____8386 =
                                                            let uu____8393 =
                                                              let uu____8394
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8395
                                                                =
                                                                let uu____8406
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____8406)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8394
                                                                uu____8395
                                                               in
                                                            let uu____8415 =
                                                              let uu____8416
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8416
                                                               in
                                                            (uu____8393,
                                                              uu____8415,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8386
                                                           in
                                                        let uu____8417 =
                                                          let uu____8420 =
                                                            let uu____8423 =
                                                              let uu____8426
                                                                =
                                                                let uu____8429
                                                                  =
                                                                  primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1
                                                                   in
                                                                FStar_List.append
                                                                  [eqn]
                                                                  uu____8429
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____8426
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____8423
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____8420
                                                           in
                                                        (uu____8417, env2))))))
                               | uu____8434 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____8497 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____8497,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____8500 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____8547  ->
                                         fun fvb  ->
                                           match uu____8547 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____8593 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8593
                                                  in
                                               let gtok =
                                                 let uu____8595 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8595
                                                  in
                                               let env4 =
                                                 let uu____8597 =
                                                   let uu____8600 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____8600
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____8597
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____8500 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____8706
                                     t_norm uu____8708 =
                                     match (uu____8706, uu____8708) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____8736;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____8737;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____8739;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____8740;_})
                                         ->
                                         let uu____8761 =
                                           let uu____8770 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____8770 with
                                           | (tcenv',uu____8788,e_t) ->
                                               let uu____8794 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____8811 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____8794 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___391_8837 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___391_8837.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____8761 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____8856 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____8856
                                                then
                                                  let uu____8857 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____8858 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____8859 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____8857 uu____8858
                                                    uu____8859
                                                else ());
                                               (let uu____8861 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____8861 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____8898 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____8898
                                                      then
                                                        let uu____8899 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____8900 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____8901 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____8902 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____8899
                                                          uu____8900
                                                          uu____8901
                                                          uu____8902
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____8906 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____8906 with
                                                      | (vars,guards,env'1,binder_decls,uu____8937)
                                                          ->
                                                          let decl_g =
                                                            let uu____8951 =
                                                              let uu____8962
                                                                =
                                                                let uu____8965
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____8965
                                                                 in
                                                              (g, uu____8962,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____8951
                                                             in
                                                          let env02 =
                                                            FStar_SMTEncoding_Env.push_zfuel_name
                                                              env01
                                                              fvb.FStar_SMTEncoding_Env.fvar_lid
                                                              g
                                                             in
                                                          let decl_g_tok =
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              (gtok, [],
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Token for fuel-instrumented partial applications"))
                                                             in
                                                          let vars_tm =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          let app =
                                                            let uu____8978 =
                                                              let uu____8985
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____8985)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____8978
                                                             in
                                                          let gsapp =
                                                            let uu____8991 =
                                                              let uu____8998
                                                                =
                                                                let uu____9001
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____9001 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____8998)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____8991
                                                             in
                                                          let gmax =
                                                            let uu____9007 =
                                                              let uu____9014
                                                                =
                                                                let uu____9017
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____9017 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____9014)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____9007
                                                             in
                                                          let body1 =
                                                            let uu____9023 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____9023
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____9025 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____9025
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____9043
                                                                   =
                                                                   let uu____9050
                                                                    =
                                                                    let uu____9051
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9052
                                                                    =
                                                                    let uu____9067
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9067)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9051
                                                                    uu____9052
                                                                     in
                                                                   let uu____9078
                                                                    =
                                                                    let uu____9079
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9079
                                                                     in
                                                                   (uu____9050,
                                                                    uu____9078,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____9043
                                                                  in
                                                               let eqn_f =
                                                                 let uu____9081
                                                                   =
                                                                   let uu____9088
                                                                    =
                                                                    let uu____9089
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9090
                                                                    =
                                                                    let uu____9101
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9101)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9089
                                                                    uu____9090
                                                                     in
                                                                   (uu____9088,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____9081
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____9111
                                                                   =
                                                                   let uu____9118
                                                                    =
                                                                    let uu____9119
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9120
                                                                    =
                                                                    let uu____9131
                                                                    =
                                                                    let uu____9132
                                                                    =
                                                                    let uu____9137
                                                                    =
                                                                    let uu____9138
                                                                    =
                                                                    let uu____9145
                                                                    =
                                                                    let uu____9148
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9148
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____9145)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____9138
                                                                     in
                                                                    (gsapp,
                                                                    uu____9137)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9132
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9131)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9119
                                                                    uu____9120
                                                                     in
                                                                   (uu____9118,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____9111
                                                                  in
                                                               let uu____9159
                                                                 =
                                                                 let uu____9168
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____9168
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____9197)
                                                                    ->
                                                                    let vars_tm1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1  in
                                                                    let gapp
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                     in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____9218
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9218
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____9219
                                                                    =
                                                                    let uu____9226
                                                                    =
                                                                    let uu____9227
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9228
                                                                    =
                                                                    let uu____9239
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____9239)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9227
                                                                    uu____9228
                                                                     in
                                                                    (uu____9226,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9219
                                                                     in
                                                                    let uu____9248
                                                                    =
                                                                    let uu____9257
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____9257
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____9272
                                                                    =
                                                                    let uu____9275
                                                                    =
                                                                    let uu____9276
                                                                    =
                                                                    let uu____9283
                                                                    =
                                                                    let uu____9284
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9285
                                                                    =
                                                                    let uu____9296
                                                                    =
                                                                    let uu____9297
                                                                    =
                                                                    let uu____9302
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____9302,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9297
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____9296)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9284
                                                                    uu____9285
                                                                     in
                                                                    (uu____9283,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9276
                                                                     in
                                                                    [uu____9275]
                                                                     in
                                                                    (d3,
                                                                    uu____9272)
                                                                     in
                                                                    (match uu____9248
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                                  in
                                                               (match uu____9159
                                                                with
                                                                | (aux_decls,g_typing)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls
                                                                    (FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                    env02))))))))
                                      in
                                   let uu____9361 =
                                     let uu____9374 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____9431  ->
                                          fun uu____9432  ->
                                            match (uu____9431, uu____9432)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____9547 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____9547 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____9374
                                      in
                                   (match uu____9361 with
                                    | (decls2,eqns,env01) ->
                                        let uu____9620 =
                                          let isDeclFun uu___374_9634 =
                                            match uu___374_9634 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____9635 -> true
                                            | uu____9646 -> false  in
                                          let uu____9647 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____9647
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____9620 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____9687 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___375_9691  ->
                                        match uu___375_9691 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____9692 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____9698 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____9698)))
                                in
                             if uu____9687
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___393_9715  ->
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
                   let uu____9750 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9750
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____9811 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9811 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9815 = encode_sigelt' env se  in
      match uu____9815 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9827 =
                  let uu____9828 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9828  in
                [uu____9827]
            | uu____9829 ->
                let uu____9830 =
                  let uu____9833 =
                    let uu____9834 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9834  in
                  uu____9833 :: g  in
                let uu____9835 =
                  let uu____9838 =
                    let uu____9839 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9839  in
                  [uu____9838]  in
                FStar_List.append uu____9830 uu____9835
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____9852 =
          let uu____9853 = FStar_Syntax_Subst.compress t  in
          uu____9853.FStar_Syntax_Syntax.n  in
        match uu____9852 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9857)) -> s = "opaque_to_smt"
        | uu____9858 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9865 =
          let uu____9866 = FStar_Syntax_Subst.compress t  in
          uu____9866.FStar_Syntax_Syntax.n  in
        match uu____9865 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9870)) -> s = "uninterpreted_by_smt"
        | uu____9871 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9876 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9881 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9892 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9893 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9894 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9907 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9909 =
            let uu____9910 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____9910  in
          if uu____9909
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9936 ->
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
               let uu____9968 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9968 with
               | (formals,uu____9988) ->
                   let arity = FStar_List.length formals  in
                   let uu____10012 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____10012 with
                    | (aname,atok,env2) ->
                        let uu____10032 =
                          let uu____10037 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____10037 env2
                           in
                        (match uu____10032 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____10049 =
                                 let uu____10050 =
                                   let uu____10061 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____10081  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____10061,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____10050
                                  in
                               [uu____10049;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____10092 =
                               let aux uu____10150 uu____10151 =
                                 match (uu____10150, uu____10151) with
                                 | ((bv,uu____10207),(env3,acc_sorts,acc)) ->
                                     let uu____10251 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____10251 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____10092 with
                              | (uu____10325,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____10348 =
                                      let uu____10355 =
                                        let uu____10356 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10357 =
                                          let uu____10368 =
                                            let uu____10369 =
                                              let uu____10374 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____10374)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____10369
                                             in
                                          ([[app]], xs_sorts, uu____10368)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10356 uu____10357
                                         in
                                      (uu____10355,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10348
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app =
                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                        tok_term xs_sorts
                                       in
                                    let uu____10386 =
                                      let uu____10393 =
                                        let uu____10394 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10395 =
                                          let uu____10406 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____10406)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10394 uu____10395
                                         in
                                      (uu____10393,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10386
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____10417 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____10417 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____10443,uu____10444)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____10445 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____10445 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____10460,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____10466 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___376_10470  ->
                      match uu___376_10470 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____10471 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____10476 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10477 -> false))
               in
            Prims.op_Negation uu____10466  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____10484 =
               let uu____10491 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____10491 env fv t quals  in
             match uu____10484 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____10506 =
                   let uu____10507 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____10507  in
                 (uu____10506, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____10513 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____10513 with
           | (uvs,f1) ->
               let env1 =
                 let uu___394_10525 = env  in
                 let uu____10526 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___394_10525.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___394_10525.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___394_10525.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____10526;
                   FStar_SMTEncoding_Env.warn =
                     (uu___394_10525.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___394_10525.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___394_10525.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___394_10525.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___394_10525.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___394_10525.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___394_10525.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____10528 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____10528 with
                | (f3,decls) ->
                    let g =
                      let uu____10542 =
                        let uu____10543 =
                          let uu____10550 =
                            let uu____10551 =
                              let uu____10552 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____10552
                               in
                            FStar_Pervasives_Native.Some uu____10551  in
                          let uu____10553 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____10550, uu____10553)  in
                        FStar_SMTEncoding_Util.mkAssume uu____10543  in
                      [uu____10542]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10555) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____10567 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____10589 =
                       let uu____10592 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____10592.FStar_Syntax_Syntax.fv_name  in
                     uu____10589.FStar_Syntax_Syntax.v  in
                   let uu____10593 =
                     let uu____10594 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____10594  in
                   if uu____10593
                   then
                     let val_decl =
                       let uu___395_10624 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___395_10624.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___395_10624.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___395_10624.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10625 = encode_sigelt' env1 val_decl  in
                     match uu____10625 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____10567 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10659,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10661;
                          FStar_Syntax_Syntax.lbtyp = uu____10662;
                          FStar_Syntax_Syntax.lbeff = uu____10663;
                          FStar_Syntax_Syntax.lbdef = uu____10664;
                          FStar_Syntax_Syntax.lbattrs = uu____10665;
                          FStar_Syntax_Syntax.lbpos = uu____10666;_}::[]),uu____10667)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10684 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10684 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10713 =
                   let uu____10716 =
                     let uu____10717 =
                       let uu____10724 =
                         let uu____10725 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10726 =
                           let uu____10737 =
                             let uu____10738 =
                               let uu____10743 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10743)  in
                             FStar_SMTEncoding_Util.mkEq uu____10738  in
                           ([[b2t_x]], [xx], uu____10737)  in
                         FStar_SMTEncoding_Term.mkForall uu____10725
                           uu____10726
                          in
                       (uu____10724,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10717  in
                   [uu____10716]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10713
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10764,uu____10765) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___377_10774  ->
                  match uu___377_10774 with
                  | FStar_Syntax_Syntax.Discriminator uu____10775 -> true
                  | uu____10776 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10777,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10788 =
                     let uu____10789 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10789.FStar_Ident.idText  in
                   uu____10788 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___378_10793  ->
                     match uu___378_10793 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10794 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10796) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___379_10807  ->
                  match uu___379_10807 with
                  | FStar_Syntax_Syntax.Projector uu____10808 -> true
                  | uu____10813 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10816 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10816 with
           | FStar_Pervasives_Native.Some uu____10823 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___396_10825 = se  in
                 let uu____10826 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10826;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___396_10825.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___396_10825.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___396_10825.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10829) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10841) ->
          let uu____10850 = encode_sigelts env ses  in
          (match uu____10850 with
           | (g,env1) ->
               let uu____10867 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___380_10890  ->
                         match uu___380_10890 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10891;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10892;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10893;_}
                             -> false
                         | uu____10896 -> true))
                  in
               (match uu____10867 with
                | (g',inversions) ->
                    let uu____10911 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___381_10932  ->
                              match uu___381_10932 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10933 ->
                                  true
                              | uu____10944 -> false))
                       in
                    (match uu____10911 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10960,tps,k,uu____10963,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___382_10980  ->
                    match uu___382_10980 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10981 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10992 = c  in
              match uu____10992 with
              | (name,args,uu____10997,uu____10998,uu____10999) ->
                  let uu____11004 =
                    let uu____11005 =
                      let uu____11016 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____11039  ->
                                match uu____11039 with
                                | (uu____11046,sort,uu____11048) -> sort))
                         in
                      (name, uu____11016, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____11005  in
                  [uu____11004]
            else
              (let uu____11052 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____11052 c)
             in
          let inversion_axioms tapp vars =
            let uu____11078 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____11084 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____11084 FStar_Option.isNone))
               in
            if uu____11078
            then []
            else
              (let uu____11116 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____11116 with
               | (xxsym,xx) ->
                   let uu____11125 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____11164  ->
                             fun l  ->
                               match uu____11164 with
                               | (out,decls) ->
                                   let uu____11184 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____11184 with
                                    | (uu____11195,data_t) ->
                                        let uu____11197 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____11197 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____11241 =
                                                 let uu____11242 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____11242.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____11241 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____11245,indices) ->
                                                   indices
                                               | uu____11271 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____11301  ->
                                                         match uu____11301
                                                         with
                                                         | (x,uu____11309) ->
                                                             let uu____11314
                                                               =
                                                               let uu____11315
                                                                 =
                                                                 let uu____11322
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____11322,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____11315
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____11314)
                                                    env)
                                                in
                                             let uu____11325 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____11325 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____11351 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____11367
                                                                 =
                                                                 let uu____11372
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____11372,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____11367)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____11351
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____11375 =
                                                      let uu____11376 =
                                                        let uu____11381 =
                                                          let uu____11382 =
                                                            let uu____11387 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____11387,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____11382
                                                           in
                                                        (out, uu____11381)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____11376
                                                       in
                                                    (uu____11375,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____11125 with
                    | (data_ax,decls) ->
                        let uu____11400 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____11400 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____11411 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____11411 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____11415 =
                                 let uu____11422 =
                                   let uu____11423 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____11424 =
                                     let uu____11435 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____11444 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____11435,
                                       uu____11444)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____11423 uu____11424
                                    in
                                 let uu____11453 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____11422,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____11453)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____11415
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____11454 =
            let uu____11459 =
              let uu____11460 = FStar_Syntax_Subst.compress k  in
              uu____11460.FStar_Syntax_Syntax.n  in
            match uu____11459 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____11495 -> (tps, k)  in
          (match uu____11454 with
           | (formals,res) ->
               let uu____11502 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11502 with
                | (formals1,res1) ->
                    let uu____11513 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____11513 with
                     | (vars,guards,env',binder_decls,uu____11538) ->
                         let arity = FStar_List.length vars  in
                         let uu____11552 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11552 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11575 =
                                  let uu____11582 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11582)  in
                                FStar_SMTEncoding_Util.mkApp uu____11575  in
                              let uu____11587 =
                                let tname_decl =
                                  let uu____11597 =
                                    let uu____11598 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11622  ->
                                              match uu____11622 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11635 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11598,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11635, false)
                                     in
                                  constructor_or_logic_type_decl uu____11597
                                   in
                                let uu____11638 =
                                  match vars with
                                  | [] ->
                                      let uu____11651 =
                                        let uu____11652 =
                                          let uu____11655 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____11655
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11652
                                         in
                                      ([], uu____11651)
                                  | uu____11666 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11673 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11673
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11687 =
                                          let uu____11694 =
                                            let uu____11695 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____11696 =
                                              let uu____11711 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11711)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____11695 uu____11696
                                             in
                                          (uu____11694,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11687
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11638 with
                                | (tok_decls,env2) ->
                                    let uu____11732 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____11732
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____11587 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11757 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11757 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11777 =
                                               let uu____11778 =
                                                 let uu____11785 =
                                                   let uu____11786 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11786
                                                    in
                                                 (uu____11785,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11778
                                                in
                                             [uu____11777]
                                           else []  in
                                         let uu____11788 =
                                           let uu____11791 =
                                             let uu____11794 =
                                               let uu____11795 =
                                                 let uu____11802 =
                                                   let uu____11803 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11804 =
                                                     let uu____11815 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11815)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11803 uu____11804
                                                    in
                                                 (uu____11802,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11795
                                                in
                                             [uu____11794]  in
                                           FStar_List.append karr uu____11791
                                            in
                                         FStar_List.append decls1 uu____11788
                                      in
                                   let aux =
                                     let uu____11827 =
                                       let uu____11830 =
                                         inversion_axioms tapp vars  in
                                       let uu____11833 =
                                         let uu____11836 =
                                           let uu____11837 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11837 env2
                                             tapp vars
                                            in
                                         [uu____11836]  in
                                       FStar_List.append uu____11830
                                         uu____11833
                                        in
                                     FStar_List.append kindingAx uu____11827
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11842,uu____11843,uu____11844,uu____11845,uu____11846)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11852,t,uu____11854,n_tps,uu____11856) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11864 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11864 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11912 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11912 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11933 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11933 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11947 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11947 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____12017 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____12017,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____12021 =
                                  let uu____12022 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____12022, true)
                                   in
                                let uu____12025 =
                                  let uu____12032 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____12032
                                   in
                                FStar_All.pipe_right uu____12021 uu____12025
                                 in
                              let app =
                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                  ddtok_tm vars
                                 in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____12043 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____12043 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____12055::uu____12056 ->
                                         let ff =
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
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____12101 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____12102 =
                                           let uu____12113 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____12113)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12101 uu____12102
                                     | uu____12132 -> tok_typing  in
                                   let uu____12141 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____12141 with
                                    | (vars',guards',env'',decls_formals,uu____12166)
                                        ->
                                        let uu____12179 =
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
                                        (match uu____12179 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____12208 ->
                                                   let uu____12217 =
                                                     let uu____12218 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____12218
                                                      in
                                                   [uu____12217]
                                                in
                                             let encode_elim uu____12232 =
                                               let uu____12233 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____12233 with
                                               | (head1,args) ->
                                                   let uu____12284 =
                                                     let uu____12285 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____12285.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____12284 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____12297;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____12298;_},uu____12299)
                                                        ->
                                                        let uu____12304 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12304
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12319
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12319
                                                              with
                                                              | (encoded_args,arg_decls)
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
                                                                    uu____12370
                                                                    ->
                                                                    let uu____12371
                                                                    =
                                                                    let uu____12376
                                                                    =
                                                                    let uu____12377
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12377
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12376)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12371
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12393
                                                                    =
                                                                    let uu____12394
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12394
                                                                     in
                                                                    if
                                                                    uu____12393
                                                                    then
                                                                    let uu____12407
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12407]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12409
                                                                    =
                                                                    let uu____12422
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12478
                                                                     ->
                                                                    fun
                                                                    uu____12479
                                                                     ->
                                                                    match 
                                                                    (uu____12478,
                                                                    uu____12479)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12584
                                                                    =
                                                                    let uu____12591
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12591
                                                                     in
                                                                    (match uu____12584
                                                                    with
                                                                    | 
                                                                    (uu____12604,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12612
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12612
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12616
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12616
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____12422
                                                                     in
                                                                  (match uu____12409
                                                                   with
                                                                   | 
                                                                   (uu____12633,arg_vars,elim_eqns_or_guards,uu____12636)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
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
                                                                    let uu____12660
                                                                    =
                                                                    let uu____12667
                                                                    =
                                                                    let uu____12668
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12669
                                                                    =
                                                                    let uu____12680
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12681
                                                                    =
                                                                    let uu____12682
                                                                    =
                                                                    let uu____12687
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12687)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12682
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12680,
                                                                    uu____12681)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12668
                                                                    uu____12669
                                                                     in
                                                                    (uu____12667,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12660
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12698
                                                                    =
                                                                    let uu____12703
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12703,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12698
                                                                     in
                                                                    let uu____12704
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12704
                                                                    then
                                                                    let x =
                                                                    let uu____12710
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12710,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12712
                                                                    =
                                                                    let uu____12719
                                                                    =
                                                                    let uu____12720
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12721
                                                                    =
                                                                    let uu____12732
                                                                    =
                                                                    let uu____12737
                                                                    =
                                                                    let uu____12740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12740]
                                                                     in
                                                                    [uu____12737]
                                                                     in
                                                                    let uu____12745
                                                                    =
                                                                    let uu____12746
                                                                    =
                                                                    let uu____12751
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12751,
                                                                    uu____12752)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12746
                                                                     in
                                                                    (uu____12732,
                                                                    [x],
                                                                    uu____12745)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12720
                                                                    uu____12721
                                                                     in
                                                                    let uu____12765
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12719,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12765)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12712
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12770
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
                                                                    (let uu____12802
                                                                    =
                                                                    let uu____12803
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12803
                                                                    dapp1  in
                                                                    [uu____12802])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12770
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12810
                                                                    =
                                                                    let uu____12817
                                                                    =
                                                                    let uu____12818
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12819
                                                                    =
                                                                    let uu____12830
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12831
                                                                    =
                                                                    let uu____12832
                                                                    =
                                                                    let uu____12837
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12837)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12832
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12830,
                                                                    uu____12831)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12818
                                                                    uu____12819
                                                                     in
                                                                    (uu____12817,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12810)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12851 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12851
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12866
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12866
                                                              with
                                                              | (encoded_args,arg_decls)
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
                                                                    uu____12917
                                                                    ->
                                                                    let uu____12918
                                                                    =
                                                                    let uu____12923
                                                                    =
                                                                    let uu____12924
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12924
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12923)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12918
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12940
                                                                    =
                                                                    let uu____12941
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12941
                                                                     in
                                                                    if
                                                                    uu____12940
                                                                    then
                                                                    let uu____12954
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12954]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12956
                                                                    =
                                                                    let uu____12969
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____13025
                                                                     ->
                                                                    fun
                                                                    uu____13026
                                                                     ->
                                                                    match 
                                                                    (uu____13025,
                                                                    uu____13026)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13131
                                                                    =
                                                                    let uu____13138
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13138
                                                                     in
                                                                    (match uu____13131
                                                                    with
                                                                    | 
                                                                    (uu____13151,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13159
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13159
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13163
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13163
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____12969
                                                                     in
                                                                  (match uu____12956
                                                                   with
                                                                   | 
                                                                   (uu____13180,arg_vars,elim_eqns_or_guards,uu____13183)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
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
                                                                    let uu____13207
                                                                    =
                                                                    let uu____13214
                                                                    =
                                                                    let uu____13215
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13216
                                                                    =
                                                                    let uu____13227
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13228
                                                                    =
                                                                    let uu____13229
                                                                    =
                                                                    let uu____13234
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13234)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13229
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13227,
                                                                    uu____13228)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13215
                                                                    uu____13216
                                                                     in
                                                                    (uu____13214,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13207
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13245
                                                                    =
                                                                    let uu____13250
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13250,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13245
                                                                     in
                                                                    let uu____13251
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13251
                                                                    then
                                                                    let x =
                                                                    let uu____13257
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13257,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13259
                                                                    =
                                                                    let uu____13266
                                                                    =
                                                                    let uu____13267
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13268
                                                                    =
                                                                    let uu____13279
                                                                    =
                                                                    let uu____13284
                                                                    =
                                                                    let uu____13287
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13287]
                                                                     in
                                                                    [uu____13284]
                                                                     in
                                                                    let uu____13292
                                                                    =
                                                                    let uu____13293
                                                                    =
                                                                    let uu____13298
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13299
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13298,
                                                                    uu____13299)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13293
                                                                     in
                                                                    (uu____13279,
                                                                    [x],
                                                                    uu____13292)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13267
                                                                    uu____13268
                                                                     in
                                                                    let uu____13312
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13266,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13312)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13259
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13317
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
                                                                    (let uu____13349
                                                                    =
                                                                    let uu____13350
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____13350
                                                                    dapp1  in
                                                                    [uu____13349])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13317
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____13357
                                                                    =
                                                                    let uu____13364
                                                                    =
                                                                    let uu____13365
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13366
                                                                    =
                                                                    let uu____13377
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13378
                                                                    =
                                                                    let uu____13379
                                                                    =
                                                                    let uu____13384
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____13384)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13379
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13377,
                                                                    uu____13378)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13365
                                                                    uu____13366
                                                                     in
                                                                    (uu____13364,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13357)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____13397 ->
                                                        ((let uu____13399 =
                                                            let uu____13404 =
                                                              let uu____13405
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____13406
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____13405
                                                                uu____13406
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____13404)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____13399);
                                                         ([], [])))
                                                in
                                             let uu____13411 = encode_elim ()
                                                in
                                             (match uu____13411 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____13437 =
                                                      let uu____13440 =
                                                        let uu____13443 =
                                                          let uu____13446 =
                                                            let uu____13449 =
                                                              let uu____13450
                                                                =
                                                                let uu____13461
                                                                  =
                                                                  let uu____13462
                                                                    =
                                                                    let uu____13463
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____13463
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____13462
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____13461)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____13450
                                                               in
                                                            [uu____13449]  in
                                                          let uu____13466 =
                                                            let uu____13469 =
                                                              let uu____13472
                                                                =
                                                                let uu____13475
                                                                  =
                                                                  let uu____13478
                                                                    =
                                                                    let uu____13481
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____13482
                                                                    =
                                                                    let uu____13485
                                                                    =
                                                                    let uu____13486
                                                                    =
                                                                    let uu____13493
                                                                    =
                                                                    let uu____13494
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13495
                                                                    =
                                                                    let uu____13506
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____13506)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13494
                                                                    uu____13495
                                                                     in
                                                                    (uu____13493,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13486
                                                                     in
                                                                    let uu____13515
                                                                    =
                                                                    let uu____13518
                                                                    =
                                                                    let uu____13519
                                                                    =
                                                                    let uu____13526
                                                                    =
                                                                    let uu____13527
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13528
                                                                    =
                                                                    let uu____13539
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____13540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____13539,
                                                                    uu____13540)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13527
                                                                    uu____13528
                                                                     in
                                                                    (uu____13526,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13519
                                                                     in
                                                                    [uu____13518]
                                                                     in
                                                                    uu____13485
                                                                    ::
                                                                    uu____13515
                                                                     in
                                                                    uu____13481
                                                                    ::
                                                                    uu____13482
                                                                     in
                                                                  FStar_List.append
                                                                    uu____13478
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____13475
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____13472
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____13469
                                                             in
                                                          FStar_List.append
                                                            uu____13446
                                                            uu____13466
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____13443
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____13440
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____13437
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____13574  ->
              fun se  ->
                match uu____13574 with
                | (g,env1) ->
                    let uu____13594 = encode_sigelt env1 se  in
                    (match uu____13594 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____13659 =
        match uu____13659 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____13691 ->
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
                 ((let uu____13697 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13697
                   then
                     let uu____13698 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13699 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13700 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13698 uu____13699 uu____13700
                   else ());
                  (let uu____13702 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13702 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13718 =
                         let uu____13725 =
                           let uu____13726 =
                             let uu____13727 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13727
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13726  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13725
                          in
                       (match uu____13718 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13741 = FStar_Options.log_queries ()
                                 in
                              if uu____13741
                              then
                                let uu____13742 =
                                  let uu____13743 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13744 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13745 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13743 uu____13744 uu____13745
                                   in
                                FStar_Pervasives_Native.Some uu____13742
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____13757,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13777 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13777 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13800 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13800 with | (uu____13823,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13836 'Auu____13837 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13836,'Auu____13837)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13906  ->
              match uu____13906 with
              | (l,uu____13918,uu____13919) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13963  ->
              match uu____13963 with
              | (l,uu____13977,uu____13978) ->
                  let uu____13987 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13988 =
                    let uu____13991 =
                      let uu____13992 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13992  in
                    [uu____13991]  in
                  uu____13987 :: uu____13988))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____14019 =
      let uu____14022 =
        let uu____14023 = FStar_Util.psmap_empty ()  in
        let uu____14038 = FStar_Util.psmap_empty ()  in
        let uu____14041 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____14044 =
          let uu____14045 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____14045 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____14023;
          FStar_SMTEncoding_Env.fvar_bindings = uu____14038;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____14041;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____14044;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____14022]  in
    FStar_ST.op_Colon_Equals last_env uu____14019
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____14079 = FStar_ST.op_Bang last_env  in
      match uu____14079 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14106 ->
          let uu___397_14109 = e  in
          let uu____14110 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___397_14109.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___397_14109.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___397_14109.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___397_14109.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___397_14109.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___397_14109.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___397_14109.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___397_14109.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____14110;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___397_14109.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____14116 = FStar_ST.op_Bang last_env  in
    match uu____14116 with
    | [] -> failwith "Empty env stack"
    | uu____14142::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____14173  ->
    let uu____14174 = FStar_ST.op_Bang last_env  in
    match uu____14174 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____14232  ->
    let uu____14233 = FStar_ST.op_Bang last_env  in
    match uu____14233 with
    | [] -> failwith "Popping an empty stack"
    | uu____14259::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____14294  -> FStar_Common.snapshot push_env last_env () 
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_env last_env depth 
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (snapshot :
  Prims.string ->
    (FStar_TypeChecker_Env.solver_depth_t,unit)
      FStar_Pervasives_Native.tuple2)
  =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____14337  ->
         let uu____14338 = snapshot_env ()  in
         match uu____14338 with
         | (env_depth,()) ->
             let uu____14354 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____14354 with
              | (varops_depth,()) ->
                  let uu____14370 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____14370 with
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
        (fun uu____14413  ->
           let uu____14414 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____14414 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____14476 = snapshot msg  in () 
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
        | (uu____14517::uu____14518,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___398_14526 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___398_14526.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___398_14526.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___398_14526.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____14527 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____14546 =
        let uu____14549 =
          let uu____14550 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____14550  in
        let uu____14551 = open_fact_db_tags env  in uu____14549 ::
          uu____14551
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____14546
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____14577 = encode_sigelt env se  in
      match uu____14577 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____14621 = FStar_Options.log_queries ()  in
        if uu____14621
        then
          let uu____14624 =
            let uu____14625 =
              let uu____14626 =
                let uu____14627 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14627 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14626  in
            FStar_SMTEncoding_Term.Caption uu____14625  in
          uu____14624 :: decls
        else decls  in
      (let uu____14638 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14638
       then
         let uu____14639 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14639
       else ());
      (let env =
         let uu____14642 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14642 tcenv  in
       let uu____14643 = encode_top_level_facts env se  in
       match uu____14643 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14657 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14657)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____14673 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14673
       then
         let uu____14674 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14674
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14715  ->
                 fun se  ->
                   match uu____14715 with
                   | (g,env2) ->
                       let uu____14735 = encode_top_level_facts env2 se  in
                       (match uu____14735 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14758 =
         encode_signature
           (let uu___399_14767 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___399_14767.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___399_14767.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___399_14767.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___399_14767.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___399_14767.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___399_14767.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___399_14767.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___399_14767.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___399_14767.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___399_14767.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14758 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14786 = FStar_Options.log_queries ()  in
             if uu____14786
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___400_14794 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___400_14794.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___400_14794.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___400_14794.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___400_14794.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___400_14794.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___400_14794.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___400_14794.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___400_14794.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___400_14794.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___400_14794.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14796 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14796
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____14854 =
           let uu____14855 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14855.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14854);
        (let env =
           let uu____14857 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14857 tcenv  in
         let uu____14858 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____14897 = aux rest  in
                 (match uu____14897 with
                  | (out,rest1) ->
                      let t =
                        let uu____14925 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14925 with
                        | FStar_Pervasives_Native.Some uu____14928 ->
                            let uu____14929 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14929
                              x.FStar_Syntax_Syntax.sort
                        | uu____14930 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14934 =
                        let uu____14937 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___401_14940 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___401_14940.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___401_14940.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14937 :: out  in
                      (uu____14934, rest1))
             | uu____14945 -> ([], bindings)  in
           let uu____14952 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____14952 with
           | (closing,bindings) ->
               let uu____14979 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14979, bindings)
            in
         match uu____14858 with
         | (q1,bindings) ->
             let uu____15010 = encode_env_bindings env bindings  in
             (match uu____15010 with
              | (env_decls,env1) ->
                  ((let uu____15032 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____15032
                    then
                      let uu____15033 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15033
                    else ());
                   (let uu____15035 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____15035 with
                    | (phi,qdecls) ->
                        let uu____15056 =
                          let uu____15061 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15061 phi
                           in
                        (match uu____15056 with
                         | (labels,phi1) ->
                             let uu____15078 = encode_labels labels  in
                             (match uu____15078 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15115 =
                                      let uu____15122 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15123 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____15122,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____15123)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15115
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
  