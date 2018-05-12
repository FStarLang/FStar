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
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
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
    [FStar_SMTEncoding_Util.mkAssume
       (true_tm, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let uu____3013 =
      let uu____3014 =
        let uu____3021 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, false_tm)
           in
        (uu____3021, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3014  in
    [uu____3013]  in
  let mk_and_interp env conj uu____3037 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3062 =
      let uu____3063 =
        let uu____3070 =
          let uu____3071 = FStar_TypeChecker_Env.get_range env  in
          let uu____3072 =
            let uu____3083 =
              let uu____3084 =
                let uu____3089 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3089, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3084  in
            ([[l_and_a_b]], [aa; bb], uu____3083)  in
          FStar_SMTEncoding_Term.mkForall uu____3071 uu____3072  in
        (uu____3070, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3063  in
    [uu____3062]  in
  let mk_or_interp env disj uu____3125 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3150 =
      let uu____3151 =
        let uu____3158 =
          let uu____3159 = FStar_TypeChecker_Env.get_range env  in
          let uu____3160 =
            let uu____3171 =
              let uu____3172 =
                let uu____3177 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3177, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3172  in
            ([[l_or_a_b]], [aa; bb], uu____3171)  in
          FStar_SMTEncoding_Term.mkForall uu____3159 uu____3160  in
        (uu____3158, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3151  in
    [uu____3150]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3238 =
      let uu____3239 =
        let uu____3246 =
          let uu____3247 = FStar_TypeChecker_Env.get_range env  in
          let uu____3248 =
            let uu____3259 =
              let uu____3260 =
                let uu____3265 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3265, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3260  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3259)  in
          FStar_SMTEncoding_Term.mkForall uu____3247 uu____3248  in
        (uu____3246, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3239  in
    [uu____3238]  in
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
    let uu____3336 =
      let uu____3337 =
        let uu____3344 =
          let uu____3345 = FStar_TypeChecker_Env.get_range env  in
          let uu____3346 =
            let uu____3357 =
              let uu____3358 =
                let uu____3363 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3363, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3358  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3357)  in
          FStar_SMTEncoding_Term.mkForall uu____3345 uu____3346  in
        (uu____3344, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3337  in
    [uu____3336]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3432 =
      let uu____3433 =
        let uu____3440 =
          let uu____3441 = FStar_TypeChecker_Env.get_range env  in
          let uu____3442 =
            let uu____3453 =
              let uu____3454 =
                let uu____3459 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3459, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3454  in
            ([[l_imp_a_b]], [aa; bb], uu____3453)  in
          FStar_SMTEncoding_Term.mkForall uu____3441 uu____3442  in
        (uu____3440, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3433  in
    [uu____3432]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3520 =
      let uu____3521 =
        let uu____3528 =
          let uu____3529 = FStar_TypeChecker_Env.get_range env  in
          let uu____3530 =
            let uu____3541 =
              let uu____3542 =
                let uu____3547 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3547, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3542  in
            ([[l_iff_a_b]], [aa; bb], uu____3541)  in
          FStar_SMTEncoding_Term.mkForall uu____3529 uu____3530  in
        (uu____3528, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3521  in
    [uu____3520]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3597 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3597  in
    let uu____3600 =
      let uu____3601 =
        let uu____3608 =
          let uu____3609 = FStar_TypeChecker_Env.get_range env  in
          let uu____3610 =
            let uu____3621 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3621)  in
          FStar_SMTEncoding_Term.mkForall uu____3609 uu____3610  in
        (uu____3608, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3601  in
    [uu____3600]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3657 =
      let uu____3658 =
        let uu____3665 =
          let uu____3666 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3666 range_ty  in
        let uu____3667 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3665, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3667)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3658  in
    [uu____3657]  in
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
        let uu____3705 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3705 x1 t  in
      let uu____3706 = FStar_TypeChecker_Env.get_range env  in
      let uu____3707 =
        let uu____3718 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3718)  in
      FStar_SMTEncoding_Term.mkForall uu____3706 uu____3707  in
    let uu____3735 =
      let uu____3736 =
        let uu____3743 =
          let uu____3744 = FStar_TypeChecker_Env.get_range env  in
          let uu____3745 =
            let uu____3756 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3756)  in
          FStar_SMTEncoding_Term.mkForall uu____3744 uu____3745  in
        (uu____3743,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3736  in
    [uu____3735]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3804 =
      let uu____3805 =
        let uu____3812 =
          let uu____3813 = FStar_TypeChecker_Env.get_range env  in
          let uu____3814 =
            let uu____3829 =
              let uu____3830 =
                let uu____3835 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3836 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3835, uu____3836)  in
              FStar_SMTEncoding_Util.mkAnd uu____3830  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3829)
             in
          FStar_SMTEncoding_Term.mkForall' uu____3813 uu____3814  in
        (uu____3812,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3805  in
    [uu____3804]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____4078 =
            FStar_Util.find_opt
              (fun uu____4114  ->
                 match uu____4114 with
                 | (l,uu____4128) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4078 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4168,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4225 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4225 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
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
              let uu____4283 =
                ((let uu____4286 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4286) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4283
              then
                let arg_sorts =
                  let uu____4296 =
                    let uu____4297 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4297.FStar_Syntax_Syntax.n  in
                  match uu____4296 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4303) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4333  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4338 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4340 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4340 with
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
                (let uu____4369 = prims.is lid  in
                 if uu____4369
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4377 = prims.mk lid vname  in
                   match uu____4377 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4404 =
                      let uu____4421 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4421 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4447 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4447
                            then
                              let uu____4450 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___104_4453 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___104_4453.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___104_4453.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___104_4453.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___104_4453.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___104_4453.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___104_4453.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___104_4453.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___104_4453.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___104_4453.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___104_4453.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___104_4453.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___104_4453.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___104_4453.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___104_4453.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___104_4453.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___104_4453.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___104_4453.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___104_4453.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___104_4453.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___104_4453.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___104_4453.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___104_4453.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___104_4453.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___104_4453.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___104_4453.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___104_4453.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___104_4453.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___104_4453.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___104_4453.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___104_4453.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___104_4453.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___104_4453.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___104_4453.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___104_4453.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___104_4453.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___104_4453.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___104_4453.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___104_4453.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4450
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4471 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4471)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4404 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4541 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4541 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4566 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___94_4622  ->
                                       match uu___94_4622 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4626 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4626 with
                                            | (uu____4647,(xxsym,uu____4649))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4667 =
                                                  let uu____4668 =
                                                    let uu____4675 =
                                                      let uu____4676 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4677 =
                                                        let uu____4688 =
                                                          let uu____4689 =
                                                            let uu____4694 =
                                                              let uu____4695
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4695
                                                               in
                                                            (vapp,
                                                              uu____4694)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4689
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4688)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4676 uu____4677
                                                       in
                                                    (uu____4675,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4668
                                                   in
                                                [uu____4667])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4706 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4706 with
                                            | (uu____4727,(xxsym,uu____4729))
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
                                                let uu____4752 =
                                                  let uu____4753 =
                                                    let uu____4760 =
                                                      let uu____4761 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4762 =
                                                        let uu____4773 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4773)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4761 uu____4762
                                                       in
                                                    (uu____4760,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4753
                                                   in
                                                [uu____4752])
                                       | uu____4782 -> []))
                                in
                             let uu____4783 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____4783 with
                              | (vars,guards,env',decls1,uu____4810) ->
                                  let uu____4823 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4836 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____4836, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____4840 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____4840 with
                                         | (g,ds) ->
                                             let uu____4853 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____4853,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____4823 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____4870 =
                                           let uu____4877 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____4877)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____4870
                                          in
                                       let uu____4882 =
                                         let vname_decl =
                                           let uu____4890 =
                                             let uu____4901 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____4917  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____4901,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____4890
                                            in
                                         let uu____4924 =
                                           let env2 =
                                             let uu___105_4930 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___105_4930.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____4931 =
                                             let uu____4932 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____4932  in
                                           if uu____4931
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____4924 with
                                         | (tok_typing,decls2) ->
                                             let uu____4946 =
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
                                                   let uu____4964 =
                                                     let uu____4965 =
                                                       let uu____4968 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_17  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_17)
                                                         uu____4968
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____4965
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____4964)
                                               | uu____4977 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____4988 =
                                                       let uu____4995 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____4995]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____4988
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____5014 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____5015 =
                                                       let uu____5026 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____5026)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____5014 uu____5015
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5036 =
                                                       let uu____5043 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____5043,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5036
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
                                                       let uu____5070 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5071 =
                                                         let uu____5082 =
                                                           let uu____5083 =
                                                             let uu____5088 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____5089 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____5088,
                                                               uu____5089)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____5083
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____5082)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5070
                                                         uu____5071
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
                                             (match uu____4946 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____4882 with
                                        | (decls2,env2) ->
                                            let uu____5134 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5144 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5144 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5159 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5159,
                                                    decls)
                                               in
                                            (match uu____5134 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5176 =
                                                     let uu____5183 =
                                                       let uu____5184 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5185 =
                                                         let uu____5196 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5196)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5184
                                                         uu____5185
                                                        in
                                                     (uu____5183,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5176
                                                    in
                                                 let freshness =
                                                   let uu____5208 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5208
                                                   then
                                                     let uu____5213 =
                                                       let uu____5214 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5215 =
                                                         let uu____5226 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5241 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5226,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5241)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5214
                                                         uu____5215
                                                        in
                                                     let uu____5244 =
                                                       let uu____5247 =
                                                         let uu____5248 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5248 env2
                                                           vapp vars
                                                          in
                                                       [uu____5247]  in
                                                     uu____5213 :: uu____5244
                                                   else []  in
                                                 let g =
                                                   let uu____5253 =
                                                     let uu____5256 =
                                                       let uu____5259 =
                                                         let uu____5262 =
                                                           let uu____5265 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5265
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5262
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5259
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5256
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5253
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5306 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5306 with
          | FStar_Pervasives_Native.None  ->
              let uu____5317 = encode_free_var false env x t t_norm []  in
              (match uu____5317 with
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
            let uu____5384 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5384 with
            | (decls,env1) ->
                let uu____5403 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5403
                then
                  let uu____5410 =
                    let uu____5413 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5413  in
                  (uu____5410, env1)
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
             (fun uu____5471  ->
                fun lb  ->
                  match uu____5471 with
                  | (decls,env1) ->
                      let uu____5491 =
                        let uu____5498 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5498
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5491 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5521 = FStar_Syntax_Util.head_and_args t  in
    match uu____5521 with
    | (hd1,args) ->
        let uu____5558 =
          let uu____5559 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5559.FStar_Syntax_Syntax.n  in
        (match uu____5558 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5563,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5582 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5588 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5616  ->
      fun quals  ->
        match uu____5616 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5708 = FStar_Util.first_N nbinders formals  in
              match uu____5708 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____5789  ->
                         fun uu____5790  ->
                           match (uu____5789, uu____5790) with
                           | ((formal,uu____5808),(binder,uu____5810)) ->
                               let uu____5819 =
                                 let uu____5826 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____5826)  in
                               FStar_Syntax_Syntax.NT uu____5819) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____5838 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____5869  ->
                              match uu____5869 with
                              | (x,i) ->
                                  let uu____5880 =
                                    let uu___106_5881 = x  in
                                    let uu____5882 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___106_5881.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___106_5881.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5882
                                    }  in
                                  (uu____5880, i)))
                       in
                    FStar_All.pipe_right uu____5838
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____5900 =
                      let uu____5905 = FStar_Syntax_Subst.compress body  in
                      let uu____5906 =
                        let uu____5907 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____5907
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____5905 uu____5906
                       in
                    uu____5900 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____5986 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____5986
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___107_5991 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___107_5991.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___107_5991.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___107_5991.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___107_5991.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___107_5991.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___107_5991.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___107_5991.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___107_5991.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___107_5991.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___107_5991.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___107_5991.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___107_5991.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___107_5991.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___107_5991.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___107_5991.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___107_5991.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___107_5991.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___107_5991.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___107_5991.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___107_5991.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___107_5991.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___107_5991.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___107_5991.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___107_5991.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___107_5991.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___107_5991.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___107_5991.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___107_5991.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___107_5991.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___107_5991.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___107_5991.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___107_5991.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___107_5991.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___107_5991.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___107_5991.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___107_5991.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___107_5991.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___107_5991.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6032 = FStar_Syntax_Util.abs_formals e  in
                match uu____6032 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6104::uu____6105 ->
                         let uu____6120 =
                           let uu____6121 =
                             let uu____6124 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6124
                              in
                           uu____6121.FStar_Syntax_Syntax.n  in
                         (match uu____6120 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6173 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6173 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6221 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6221
                                   then
                                     let uu____6260 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6260 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6358  ->
                                                   fun uu____6359  ->
                                                     match (uu____6358,
                                                             uu____6359)
                                                     with
                                                     | ((x,uu____6377),
                                                        (b,uu____6379)) ->
                                                         let uu____6388 =
                                                           let uu____6395 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6395)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6388)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6403 =
                                            let uu____6428 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6428)  in
                                          (uu____6403, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6510 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6510 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6651) ->
                              let uu____6656 =
                                let uu____6681 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6681  in
                              (uu____6656, true)
                          | uu____6758 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____6760 ->
                              let uu____6761 =
                                let uu____6762 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6763 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6762 uu____6763
                                 in
                              failwith uu____6761)
                     | uu____6792 ->
                         let rec aux' t_norm2 =
                           let uu____6827 =
                             let uu____6828 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6828.FStar_Syntax_Syntax.n  in
                           match uu____6827 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6877 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6877 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____6915 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____6915 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7019) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7024 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____7088 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____7088
               then encode_top_level_vals env bindings quals
               else
                 (let uu____7100 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____7163  ->
                            fun lb  ->
                              match uu____7163 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____7218 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____7218
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____7221 =
                                      let uu____7230 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____7230
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____7221 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____7100 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7355 =
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
                        | uu____7361 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7369 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7369 vars)
                            else
                              (let uu____7371 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7371)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7431;
                             FStar_Syntax_Syntax.lbeff = uu____7432;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7434;
                             FStar_Syntax_Syntax.lbpos = uu____7435;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7459 =
                              let uu____7468 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7468 with
                              | (tcenv',uu____7486,e_t) ->
                                  let uu____7492 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7509 -> failwith "Impossible"  in
                                  (match uu____7492 with
                                   | (e1,t_norm1) ->
                                       ((let uu___110_7535 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___110_7535.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___110_7535.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___110_7535.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___110_7535.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___110_7535.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____7459 with
                             | (env',e1,t_norm1) ->
                                 let uu____7549 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7549 with
                                  | ((binders,body,uu____7570,t_body),curry)
                                      ->
                                      ((let uu____7582 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7582
                                        then
                                          let uu____7583 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7584 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7583 uu____7584
                                        else ());
                                       (let uu____7586 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7586 with
                                        | (vars,guards,env'1,binder_decls,uu____7613)
                                            ->
                                            let body1 =
                                              let uu____7627 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7627
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None)
                                               in
                                            let app =
                                              let uu____7648 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7648 curry fvb
                                                vars
                                               in
                                            let uu____7649 =
                                              let is_logical =
                                                let uu____7659 =
                                                  let uu____7660 =
                                                    FStar_Syntax_Subst.compress
                                                      t_body
                                                     in
                                                  uu____7660.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____7659 with
                                                | FStar_Syntax_Syntax.Tm_fvar
                                                    fv when
                                                    FStar_Syntax_Syntax.fv_eq_lid
                                                      fv
                                                      FStar_Parser_Const.logical_lid
                                                    -> true
                                                | uu____7664 -> false  in
                                              (let uu____7666 =
                                                 ((FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic))
                                                    &&
                                                    (Prims.op_Negation
                                                       is_logical))
                                                   &&
                                                   (FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env2.FStar_SMTEncoding_Env.tcenv)
                                                      (FStar_Options.Other
                                                         "Logical"))
                                                  in
                                               if uu____7666
                                               then
                                                 let module_name =
                                                   let uu____7670 =
                                                     let uu____7671 =
                                                       FStar_All.pipe_right
                                                         lbn FStar_Util.right
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____7671
                                                       FStar_Syntax_Syntax.lid_of_fv
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7670
                                                     (fun l  ->
                                                        l.FStar_Ident.nsstr)
                                                    in
                                                 (if
                                                    ((module_name =
                                                        FStar_Parser_Const.prims_lid.FStar_Ident.str)
                                                       ||
                                                       (module_name =
                                                          FStar_Parser_Const.pervasives_native_lid.FStar_Ident.str))
                                                      ||
                                                      (module_name =
                                                         FStar_Parser_Const.pervasives_lid.FStar_Ident.str)
                                                  then ()
                                                  else
                                                    (let uu____7679 =
                                                       FStar_Syntax_Print.lbname_to_string
                                                         lbn
                                                        in
                                                     FStar_Util.print1
                                                       "%s does not have the logical type but has the logic qualifier, consider removing its result type annotation"
                                                       uu____7679))
                                               else ());
                                              (let uu____7681 =
                                                 (FStar_All.pipe_right quals
                                                    (FStar_List.contains
                                                       FStar_Syntax_Syntax.Logic))
                                                   || is_logical
                                                  in
                                               if uu____7681
                                               then
                                                 let uu____7692 =
                                                   FStar_SMTEncoding_Term.mk_Valid
                                                     app
                                                    in
                                                 let uu____7693 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_formula
                                                     body1 env'1
                                                    in
                                                 (uu____7692, uu____7693)
                                               else
                                                 (let uu____7703 =
                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                      body1 env'1
                                                     in
                                                  (app, uu____7703)))
                                               in
                                            (match uu____7649 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7726 =
                                                     let uu____7733 =
                                                       let uu____7734 =
                                                         FStar_Syntax_Util.range_of_lbname
                                                           lbn
                                                          in
                                                       let uu____7735 =
                                                         let uu____7746 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7746)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7734
                                                         uu____7735
                                                        in
                                                     let uu____7755 =
                                                       let uu____7756 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7756
                                                        in
                                                     (uu____7733, uu____7755,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7726
                                                    in
                                                 let uu____7757 =
                                                   let uu____7760 =
                                                     let uu____7763 =
                                                       let uu____7766 =
                                                         let uu____7769 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7769
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7766
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7763
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7760
                                                    in
                                                 (uu____7757, env2))))))
                        | uu____7774 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7837 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7837, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7840 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7887  ->
                                  fun fvb  ->
                                    match uu____7887 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7933 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7933
                                           in
                                        let gtok =
                                          let uu____7935 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7935
                                           in
                                        let env4 =
                                          let uu____7937 =
                                            let uu____7940 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_18  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_18) uu____7940
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7937
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7840 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____8046 t_norm
                              uu____8048 =
                              match (uu____8046, uu____8048) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____8076;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____8077;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____8079;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____8080;_})
                                  ->
                                  let uu____8101 =
                                    let uu____8110 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____8110 with
                                    | (tcenv',uu____8128,e_t) ->
                                        let uu____8134 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____8151 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____8134 with
                                         | (e1,t_norm1) ->
                                             ((let uu___111_8177 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___111_8177.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____8101 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____8196 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____8196
                                         then
                                           let uu____8197 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____8198 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____8199 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____8197 uu____8198 uu____8199
                                         else ());
                                        (let uu____8201 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____8201 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____8238 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8238
                                               then
                                                 let uu____8239 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8240 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8241 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____8242 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____8239 uu____8240
                                                   uu____8241 uu____8242
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____8246 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8246 with
                                               | (vars,guards,env'1,binder_decls,uu____8277)
                                                   ->
                                                   let decl_g =
                                                     let uu____8291 =
                                                       let uu____8302 =
                                                         let uu____8305 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____8305
                                                          in
                                                       (g, uu____8302,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____8291
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
                                                     let uu____8318 =
                                                       let uu____8325 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____8325)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8318
                                                      in
                                                   let gsapp =
                                                     let uu____8331 =
                                                       let uu____8338 =
                                                         let uu____8341 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____8341 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8338)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8331
                                                      in
                                                   let gmax =
                                                     let uu____8347 =
                                                       let uu____8354 =
                                                         let uu____8357 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____8357 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8354)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8347
                                                      in
                                                   let body1 =
                                                     let uu____8363 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8363
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____8365 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____8365 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8383 =
                                                            let uu____8390 =
                                                              let uu____8391
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8392
                                                                =
                                                                let uu____8407
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8407)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall'
                                                                uu____8391
                                                                uu____8392
                                                               in
                                                            let uu____8418 =
                                                              let uu____8419
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8419
                                                               in
                                                            (uu____8390,
                                                              uu____8418,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8383
                                                           in
                                                        let eqn_f =
                                                          let uu____8421 =
                                                            let uu____8428 =
                                                              let uu____8429
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8430
                                                                =
                                                                let uu____8441
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8441)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8429
                                                                uu____8430
                                                               in
                                                            (uu____8428,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8421
                                                           in
                                                        let eqn_g' =
                                                          let uu____8451 =
                                                            let uu____8458 =
                                                              let uu____8459
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8460
                                                                =
                                                                let uu____8471
                                                                  =
                                                                  let uu____8472
                                                                    =
                                                                    let uu____8477
                                                                    =
                                                                    let uu____8478
                                                                    =
                                                                    let uu____8485
                                                                    =
                                                                    let uu____8488
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8488
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8485)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8478
                                                                     in
                                                                    (gsapp,
                                                                    uu____8477)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8472
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8471)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8459
                                                                uu____8460
                                                               in
                                                            (uu____8458,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8451
                                                           in
                                                        let uu____8499 =
                                                          let uu____8508 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8508
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8537)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____8558
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8558
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8559
                                                                  =
                                                                  let uu____8566
                                                                    =
                                                                    let uu____8567
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8568
                                                                    =
                                                                    let uu____8579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8579)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8567
                                                                    uu____8568
                                                                     in
                                                                  (uu____8566,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8559
                                                                 in
                                                              let uu____8588
                                                                =
                                                                let uu____8597
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8597
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8612
                                                                    =
                                                                    let uu____8615
                                                                    =
                                                                    let uu____8616
                                                                    =
                                                                    let uu____8623
                                                                    =
                                                                    let uu____8624
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8625
                                                                    =
                                                                    let uu____8636
                                                                    =
                                                                    let uu____8637
                                                                    =
                                                                    let uu____8642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8642,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8637
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8636)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8624
                                                                    uu____8625
                                                                     in
                                                                    (uu____8623,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8616
                                                                     in
                                                                    [uu____8615]
                                                                     in
                                                                    (d3,
                                                                    uu____8612)
                                                                 in
                                                              (match uu____8588
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____8499
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
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
                            let uu____8701 =
                              let uu____8714 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8771  ->
                                   fun uu____8772  ->
                                     match (uu____8771, uu____8772) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8887 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8887 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8714
                               in
                            (match uu____8701 with
                             | (decls2,eqns,env01) ->
                                 let uu____8960 =
                                   let isDeclFun uu___95_8974 =
                                     match uu___95_8974 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____8975 -> true
                                     | uu____8986 -> false  in
                                   let uu____8987 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____8987
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____8960 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____9027 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___96_9031  ->
                                 match uu___96_9031 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9032 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____9038 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____9038)))
                         in
                      if uu____9027
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks_fvbs
                               env1
                           else
                             encode_rec_lbdefs bindings typs1 toks_fvbs env1
                         with
                         | FStar_SMTEncoding_Env.Inner_let_rec  ->
                             (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____9090 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9090
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
        let uu____9151 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9151 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9155 = encode_sigelt' env se  in
      match uu____9155 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9167 =
                  let uu____9168 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9168  in
                [uu____9167]
            | uu____9169 ->
                let uu____9170 =
                  let uu____9173 =
                    let uu____9174 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9174  in
                  uu____9173 :: g  in
                let uu____9175 =
                  let uu____9178 =
                    let uu____9179 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9179  in
                  [uu____9178]  in
                FStar_List.append uu____9170 uu____9175
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
        let uu____9192 =
          let uu____9193 = FStar_Syntax_Subst.compress t  in
          uu____9193.FStar_Syntax_Syntax.n  in
        match uu____9192 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9197)) -> s = "opaque_to_smt"
        | uu____9198 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9205 =
          let uu____9206 = FStar_Syntax_Subst.compress t  in
          uu____9206.FStar_Syntax_Syntax.n  in
        match uu____9205 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9210)) -> s = "uninterpreted_by_smt"
        | uu____9211 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9216 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9221 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9232 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9233 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9234 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9247 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9249 =
            let uu____9250 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____9250 Prims.op_Negation  in
          if uu____9249
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9276 ->
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
               let uu____9306 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9306 with
               | (formals,uu____9324) ->
                   let arity = FStar_List.length formals  in
                   let uu____9342 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9342 with
                    | (aname,atok,env2) ->
                        let uu____9362 =
                          let uu____9367 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9367
                            env2
                           in
                        (match uu____9362 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9379 =
                                 let uu____9380 =
                                   let uu____9391 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9407  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9391,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9380
                                  in
                               [uu____9379;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9416 =
                               let aux uu____9472 uu____9473 =
                                 match (uu____9472, uu____9473) with
                                 | ((bv,uu____9525),(env3,acc_sorts,acc)) ->
                                     let uu____9563 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9563 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9416 with
                              | (uu____9635,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9658 =
                                      let uu____9665 =
                                        let uu____9666 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9667 =
                                          let uu____9678 =
                                            let uu____9679 =
                                              let uu____9684 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9684)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9679
                                             in
                                          ([[app]], xs_sorts, uu____9678)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9666 uu____9667
                                         in
                                      (uu____9665,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9658
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
                                    let uu____9696 =
                                      let uu____9703 =
                                        let uu____9704 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9705 =
                                          let uu____9716 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9716)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9704 uu____9705
                                         in
                                      (uu____9703,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9696
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9727 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9727 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9753,uu____9754) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9755 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9755 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9770,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9776 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___97_9780  ->
                      match uu___97_9780 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9781 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9786 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9787 -> false))
               in
            Prims.op_Negation uu____9776  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9794 =
               let uu____9801 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9801 env fv t quals  in
             match uu____9794 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9816 =
                   let uu____9817 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9817  in
                 (uu____9816, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9823 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9823 with
           | (uvs,f1) ->
               let env1 =
                 let uu___114_9835 = env  in
                 let uu____9836 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___114_9835.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___114_9835.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___114_9835.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____9836;
                   FStar_SMTEncoding_Env.warn =
                     (uu___114_9835.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___114_9835.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___114_9835.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___114_9835.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___114_9835.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___114_9835.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___114_9835.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____9838 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____9838 with
                | (f3,decls) ->
                    let g =
                      let uu____9852 =
                        let uu____9853 =
                          let uu____9860 =
                            let uu____9861 =
                              let uu____9862 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9862
                               in
                            FStar_Pervasives_Native.Some uu____9861  in
                          let uu____9863 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____9860, uu____9863)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9853  in
                      [uu____9852]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9865) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____9877 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____9899 =
                       let uu____9902 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____9902.FStar_Syntax_Syntax.fv_name  in
                     uu____9899.FStar_Syntax_Syntax.v  in
                   let uu____9903 =
                     let uu____9904 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____9904  in
                   if uu____9903
                   then
                     let val_decl =
                       let uu___115_9934 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___115_9934.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___115_9934.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___115_9934.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____9935 = encode_sigelt' env1 val_decl  in
                     match uu____9935 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____9877 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____9969,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                         FStar_Syntax_Syntax.lbunivs = uu____9971;
                         FStar_Syntax_Syntax.lbtyp = uu____9972;
                         FStar_Syntax_Syntax.lbeff = uu____9973;
                         FStar_Syntax_Syntax.lbdef = uu____9974;
                         FStar_Syntax_Syntax.lbattrs = uu____9975;
                         FStar_Syntax_Syntax.lbpos = uu____9976;_}::[]),uu____9977)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____9994 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____9994 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10023 =
                   let uu____10026 =
                     let uu____10027 =
                       let uu____10034 =
                         let uu____10035 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10036 =
                           let uu____10047 =
                             let uu____10048 =
                               let uu____10053 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10053)  in
                             FStar_SMTEncoding_Util.mkEq uu____10048  in
                           ([[b2t_x]], [xx], uu____10047)  in
                         FStar_SMTEncoding_Term.mkForall uu____10035
                           uu____10036
                          in
                       (uu____10034,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10027  in
                   [uu____10026]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10023
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10074,uu____10075) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___98_10084  ->
                  match uu___98_10084 with
                  | FStar_Syntax_Syntax.Discriminator uu____10085 -> true
                  | uu____10086 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10087,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10098 =
                     let uu____10099 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10099.FStar_Ident.idText  in
                   uu____10098 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___99_10103  ->
                     match uu___99_10103 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10104 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10106) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_10117  ->
                  match uu___100_10117 with
                  | FStar_Syntax_Syntax.Projector uu____10118 -> true
                  | uu____10123 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10126 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10126 with
           | FStar_Pervasives_Native.Some uu____10133 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___116_10135 = se  in
                 let uu____10136 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10136;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___116_10135.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___116_10135.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___116_10135.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10139) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10151) ->
          let uu____10160 = encode_sigelts env ses  in
          (match uu____10160 with
           | (g,env1) ->
               let uu____10177 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___101_10200  ->
                         match uu___101_10200 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10201;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10202;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10203;_}
                             -> false
                         | uu____10206 -> true))
                  in
               (match uu____10177 with
                | (g',inversions) ->
                    let uu____10221 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___102_10242  ->
                              match uu___102_10242 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10243 ->
                                  true
                              | uu____10254 -> false))
                       in
                    (match uu____10221 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10270,tps,k,uu____10273,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___103_10290  ->
                    match uu___103_10290 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10291 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10302 = c  in
              match uu____10302 with
              | (name,args,uu____10307,uu____10308,uu____10309) ->
                  let uu____10314 =
                    let uu____10315 =
                      let uu____10326 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10349  ->
                                match uu____10349 with
                                | (uu____10356,sort,uu____10358) -> sort))
                         in
                      (name, uu____10326, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10315  in
                  [uu____10314]
            else
              (let uu____10362 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____10362 c)
             in
          let inversion_axioms tapp vars =
            let uu____10388 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10394 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10394 FStar_Option.isNone))
               in
            if uu____10388
            then []
            else
              (let uu____10426 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10426 with
               | (xxsym,xx) ->
                   let uu____10435 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10474  ->
                             fun l  ->
                               match uu____10474 with
                               | (out,decls) ->
                                   let uu____10494 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10494 with
                                    | (uu____10505,data_t) ->
                                        let uu____10507 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10507 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10545 =
                                                 let uu____10546 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10546.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10545 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10549,indices) ->
                                                   indices
                                               | uu____10571 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10595  ->
                                                         match uu____10595
                                                         with
                                                         | (x,uu____10601) ->
                                                             let uu____10602
                                                               =
                                                               let uu____10603
                                                                 =
                                                                 let uu____10610
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10610,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10603
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10602)
                                                    env)
                                                in
                                             let uu____10613 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10613 with
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
                                                      let uu____10639 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10655
                                                                 =
                                                                 let uu____10660
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10660,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10655)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10639
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10663 =
                                                      let uu____10664 =
                                                        let uu____10669 =
                                                          let uu____10670 =
                                                            let uu____10675 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10675,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10670
                                                           in
                                                        (out, uu____10669)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10664
                                                       in
                                                    (uu____10663,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10435 with
                    | (data_ax,decls) ->
                        let uu____10688 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10688 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10699 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10699 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10703 =
                                 let uu____10710 =
                                   let uu____10711 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____10712 =
                                     let uu____10723 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10732 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10723,
                                       uu____10732)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____10711 uu____10712
                                    in
                                 let uu____10741 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10710,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10741)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10703
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10742 =
            let uu____10747 =
              let uu____10748 = FStar_Syntax_Subst.compress k  in
              uu____10748.FStar_Syntax_Syntax.n  in
            match uu____10747 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10777 -> (tps, k)  in
          (match uu____10742 with
           | (formals,res) ->
               let uu____10784 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____10784 with
                | (formals1,res1) ->
                    let uu____10795 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____10795 with
                     | (vars,guards,env',binder_decls,uu____10820) ->
                         let arity = FStar_List.length vars  in
                         let uu____10834 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____10834 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____10857 =
                                  let uu____10864 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____10864)  in
                                FStar_SMTEncoding_Util.mkApp uu____10857  in
                              let uu____10869 =
                                let tname_decl =
                                  let uu____10879 =
                                    let uu____10880 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____10904  ->
                                              match uu____10904 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____10917 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____10880,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____10917, false)
                                     in
                                  constructor_or_logic_type_decl uu____10879
                                   in
                                let uu____10920 =
                                  match vars with
                                  | [] ->
                                      let uu____10933 =
                                        let uu____10934 =
                                          let uu____10937 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_19  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_19) uu____10937
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____10934
                                         in
                                      ([], uu____10933)
                                  | uu____10948 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____10955 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____10955
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____10969 =
                                          let uu____10976 =
                                            let uu____10977 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____10978 =
                                              let uu____10993 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____10993)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____10977 uu____10978
                                             in
                                          (uu____10976,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10969
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____10920 with
                                | (tok_decls,env2) ->
                                    let uu____11014 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____11014
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____10869 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11039 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11039 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11057 =
                                               let uu____11058 =
                                                 let uu____11065 =
                                                   let uu____11066 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11066
                                                    in
                                                 (uu____11065,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11058
                                                in
                                             [uu____11057]
                                           else []  in
                                         let uu____11068 =
                                           let uu____11071 =
                                             let uu____11074 =
                                               let uu____11075 =
                                                 let uu____11082 =
                                                   let uu____11083 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11084 =
                                                     let uu____11095 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11095)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11083 uu____11084
                                                    in
                                                 (uu____11082,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11075
                                                in
                                             [uu____11074]  in
                                           FStar_List.append karr uu____11071
                                            in
                                         FStar_List.append decls1 uu____11068
                                      in
                                   let aux =
                                     let uu____11107 =
                                       let uu____11110 =
                                         inversion_axioms tapp vars  in
                                       let uu____11113 =
                                         let uu____11116 =
                                           let uu____11117 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11117 env2
                                             tapp vars
                                            in
                                         [uu____11116]  in
                                       FStar_List.append uu____11110
                                         uu____11113
                                        in
                                     FStar_List.append kindingAx uu____11107
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11122,uu____11123,uu____11124,uu____11125,uu____11126)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11132,t,uu____11134,n_tps,uu____11136) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11144 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11144 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11184 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11184 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11205 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11205 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11219 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11219 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11289 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11289,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11293 =
                                  let uu____11294 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11294, true)
                                   in
                                let uu____11297 =
                                  let uu____11304 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____11304
                                   in
                                FStar_All.pipe_right uu____11293 uu____11297
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
                              let uu____11315 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11315 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11327::uu____11328 ->
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
                                         let uu____11373 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____11374 =
                                           let uu____11385 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11385)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11373 uu____11374
                                     | uu____11404 -> tok_typing  in
                                   let uu____11413 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11413 with
                                    | (vars',guards',env'',decls_formals,uu____11438)
                                        ->
                                        let uu____11451 =
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
                                        (match uu____11451 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11478 ->
                                                   let uu____11485 =
                                                     let uu____11486 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11486
                                                      in
                                                   [uu____11485]
                                                in
                                             let encode_elim uu____11500 =
                                               let uu____11501 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11501 with
                                               | (head1,args) ->
                                                   let uu____11546 =
                                                     let uu____11547 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11547.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11546 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11559;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11560;_},uu____11561)
                                                        ->
                                                        let uu____11566 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11566
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11581
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11581
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
                                                                    uu____11632
                                                                    ->
                                                                    let uu____11633
                                                                    =
                                                                    let uu____11638
                                                                    =
                                                                    let uu____11639
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11639
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11638)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11633
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11655
                                                                    =
                                                                    let uu____11656
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11656
                                                                     in
                                                                    if
                                                                    uu____11655
                                                                    then
                                                                    let uu____11669
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11669]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11671
                                                                    =
                                                                    let uu____11684
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11734
                                                                     ->
                                                                    fun
                                                                    uu____11735
                                                                     ->
                                                                    match 
                                                                    (uu____11734,
                                                                    uu____11735)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____11830
                                                                    =
                                                                    let uu____11837
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____11837
                                                                     in
                                                                    (match uu____11830
                                                                    with
                                                                    | 
                                                                    (uu____11850,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____11858
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____11858
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____11860
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____11860
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
                                                                    uu____11684
                                                                     in
                                                                  (match uu____11671
                                                                   with
                                                                   | 
                                                                   (uu____11877,arg_vars,elim_eqns_or_guards,uu____11880)
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
                                                                    let uu____11904
                                                                    =
                                                                    let uu____11911
                                                                    =
                                                                    let uu____11912
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____11913
                                                                    =
                                                                    let uu____11924
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____11925
                                                                    =
                                                                    let uu____11926
                                                                    =
                                                                    let uu____11931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____11931)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11926
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11924,
                                                                    uu____11925)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11912
                                                                    uu____11913
                                                                     in
                                                                    (uu____11911,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11904
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____11942
                                                                    =
                                                                    let uu____11947
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____11947,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____11942
                                                                     in
                                                                    let uu____11948
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____11948
                                                                    then
                                                                    let x =
                                                                    let uu____11954
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____11954,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____11956
                                                                    =
                                                                    let uu____11963
                                                                    =
                                                                    let uu____11964
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____11965
                                                                    =
                                                                    let uu____11976
                                                                    =
                                                                    let uu____11981
                                                                    =
                                                                    let uu____11984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____11984]
                                                                     in
                                                                    [uu____11981]
                                                                     in
                                                                    let uu____11989
                                                                    =
                                                                    let uu____11990
                                                                    =
                                                                    let uu____11995
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____11996
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____11995,
                                                                    uu____11996)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11990
                                                                     in
                                                                    (uu____11976,
                                                                    [x],
                                                                    uu____11989)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11964
                                                                    uu____11965
                                                                     in
                                                                    let uu____12009
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____11963,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12009)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11956
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12014
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
                                                                    (let uu____12046
                                                                    =
                                                                    let uu____12047
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12047
                                                                    dapp1  in
                                                                    [uu____12046])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12014
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12054
                                                                    =
                                                                    let uu____12061
                                                                    =
                                                                    let uu____12062
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12063
                                                                    =
                                                                    let uu____12074
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12075
                                                                    =
                                                                    let uu____12076
                                                                    =
                                                                    let uu____12081
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12081)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12076
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12074,
                                                                    uu____12075)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12062
                                                                    uu____12063
                                                                     in
                                                                    (uu____12061,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12054)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12095 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12095
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12110
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12110
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
                                                                    uu____12161
                                                                    ->
                                                                    let uu____12162
                                                                    =
                                                                    let uu____12167
                                                                    =
                                                                    let uu____12168
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12168
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12167)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12162
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12184
                                                                    =
                                                                    let uu____12185
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12185
                                                                     in
                                                                    if
                                                                    uu____12184
                                                                    then
                                                                    let uu____12198
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12198]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12200
                                                                    =
                                                                    let uu____12213
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12263
                                                                     ->
                                                                    fun
                                                                    uu____12264
                                                                     ->
                                                                    match 
                                                                    (uu____12263,
                                                                    uu____12264)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12359
                                                                    =
                                                                    let uu____12366
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12366
                                                                     in
                                                                    (match uu____12359
                                                                    with
                                                                    | 
                                                                    (uu____12379,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12387
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12387
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12389
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12389
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
                                                                    uu____12213
                                                                     in
                                                                  (match uu____12200
                                                                   with
                                                                   | 
                                                                   (uu____12406,arg_vars,elim_eqns_or_guards,uu____12409)
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
                                                                    let uu____12433
                                                                    =
                                                                    let uu____12440
                                                                    =
                                                                    let uu____12441
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12442
                                                                    =
                                                                    let uu____12453
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12454
                                                                    =
                                                                    let uu____12455
                                                                    =
                                                                    let uu____12460
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12460)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12455
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12453,
                                                                    uu____12454)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12441
                                                                    uu____12442
                                                                     in
                                                                    (uu____12440,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12433
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12471
                                                                    =
                                                                    let uu____12476
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12476,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12471
                                                                     in
                                                                    let uu____12477
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12477
                                                                    then
                                                                    let x =
                                                                    let uu____12483
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12483,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12485
                                                                    =
                                                                    let uu____12492
                                                                    =
                                                                    let uu____12493
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12494
                                                                    =
                                                                    let uu____12505
                                                                    =
                                                                    let uu____12510
                                                                    =
                                                                    let uu____12513
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12513]
                                                                     in
                                                                    [uu____12510]
                                                                     in
                                                                    let uu____12518
                                                                    =
                                                                    let uu____12519
                                                                    =
                                                                    let uu____12524
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12525
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12524,
                                                                    uu____12525)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12519
                                                                     in
                                                                    (uu____12505,
                                                                    [x],
                                                                    uu____12518)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12493
                                                                    uu____12494
                                                                     in
                                                                    let uu____12538
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12492,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12538)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12485
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12543
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
                                                                    (let uu____12575
                                                                    =
                                                                    let uu____12576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12576
                                                                    dapp1  in
                                                                    [uu____12575])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12543
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12583
                                                                    =
                                                                    let uu____12590
                                                                    =
                                                                    let uu____12591
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12592
                                                                    =
                                                                    let uu____12603
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12604
                                                                    =
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12610
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12610)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12605
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12603,
                                                                    uu____12604)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12591
                                                                    uu____12592
                                                                     in
                                                                    (uu____12590,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12583)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____12623 ->
                                                        ((let uu____12625 =
                                                            let uu____12630 =
                                                              let uu____12631
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____12632
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____12631
                                                                uu____12632
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____12630)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____12625);
                                                         ([], [])))
                                                in
                                             let uu____12637 = encode_elim ()
                                                in
                                             (match uu____12637 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____12663 =
                                                      let uu____12666 =
                                                        let uu____12669 =
                                                          let uu____12672 =
                                                            let uu____12675 =
                                                              let uu____12676
                                                                =
                                                                let uu____12687
                                                                  =
                                                                  let uu____12688
                                                                    =
                                                                    let uu____12689
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____12689
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12688
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____12687)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____12676
                                                               in
                                                            [uu____12675]  in
                                                          let uu____12692 =
                                                            let uu____12695 =
                                                              let uu____12698
                                                                =
                                                                let uu____12701
                                                                  =
                                                                  let uu____12704
                                                                    =
                                                                    let uu____12707
                                                                    =
                                                                    let uu____12710
                                                                    =
                                                                    let uu____12711
                                                                    =
                                                                    let uu____12718
                                                                    =
                                                                    let uu____12719
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12720
                                                                    =
                                                                    let uu____12731
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12731)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12719
                                                                    uu____12720
                                                                     in
                                                                    (uu____12718,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12711
                                                                     in
                                                                    let uu____12740
                                                                    =
                                                                    let uu____12743
                                                                    =
                                                                    let uu____12744
                                                                    =
                                                                    let uu____12751
                                                                    =
                                                                    let uu____12752
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12753
                                                                    =
                                                                    let uu____12764
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____12765
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____12764,
                                                                    uu____12765)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12752
                                                                    uu____12753
                                                                     in
                                                                    (uu____12751,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12744
                                                                     in
                                                                    [uu____12743]
                                                                     in
                                                                    uu____12710
                                                                    ::
                                                                    uu____12740
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____12707
                                                                     in
                                                                  FStar_List.append
                                                                    uu____12704
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____12701
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____12698
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____12695
                                                             in
                                                          FStar_List.append
                                                            uu____12672
                                                            uu____12692
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____12669
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____12666
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____12663
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
           (fun uu____12799  ->
              fun se  ->
                match uu____12799 with
                | (g,env1) ->
                    let uu____12819 = encode_sigelt env1 se  in
                    (match uu____12819 with
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
      let encode_binding b uu____12884 =
        match uu____12884 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____12916 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses]
                     env1.FStar_SMTEncoding_Env.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____12922 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____12922
                   then
                     let uu____12923 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____12924 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____12925 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____12923 uu____12924 uu____12925
                   else ());
                  (let uu____12927 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____12927 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12943 =
                         let uu____12950 =
                           let uu____12951 =
                             let uu____12952 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____12952
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____12951  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____12950
                          in
                       (match uu____12943 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____12966 = FStar_Options.log_queries ()
                                 in
                              if uu____12966
                              then
                                let uu____12967 =
                                  let uu____12968 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____12969 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____12970 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____12968 uu____12969 uu____12970
                                   in
                                FStar_Pervasives_Native.Some uu____12967
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____12982,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13002 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13002 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13025 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13025 with | (uu____13048,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13061 'Auu____13062 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13061,'Auu____13062)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13131  ->
              match uu____13131 with
              | (l,uu____13143,uu____13144) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13188  ->
              match uu____13188 with
              | (l,uu____13202,uu____13203) ->
                  let uu____13212 =
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_SMTEncoding_Term.Echo _0_20)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13213 =
                    let uu____13216 =
                      let uu____13217 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13217  in
                    [uu____13216]  in
                  uu____13212 :: uu____13213))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13244 =
      let uu____13247 =
        let uu____13248 = FStar_Util.psmap_empty ()  in
        let uu____13263 = FStar_Util.psmap_empty ()  in
        let uu____13266 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13269 =
          let uu____13270 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13270 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13248;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13263;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13266;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13269;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13247]  in
    FStar_ST.op_Colon_Equals last_env uu____13244
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13308 = FStar_ST.op_Bang last_env  in
      match uu____13308 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13339 ->
          let uu___117_13342 = e  in
          let uu____13343 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___117_13342.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___117_13342.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___117_13342.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___117_13342.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___117_13342.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___117_13342.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___117_13342.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___117_13342.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13343;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___117_13342.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13349 = FStar_ST.op_Bang last_env  in
    match uu____13349 with
    | [] -> failwith "Empty env stack"
    | uu____13379::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13414  ->
    let uu____13415 = FStar_ST.op_Bang last_env  in
    match uu____13415 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top =
          let uu___118_13450 = hd1  in
          let uu____13451 =
            FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___118_13450.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___118_13450.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___118_13450.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___118_13450.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___118_13450.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = uu____13451;
            FStar_SMTEncoding_Env.nolabels =
              (uu___118_13450.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___118_13450.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___118_13450.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___118_13450.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___118_13450.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13485  ->
    let uu____13486 = FStar_ST.op_Bang last_env  in
    match uu____13486 with
    | [] -> failwith "Popping an empty stack"
    | uu____13516::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____13555  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____13598  ->
         let uu____13599 = snapshot_env ()  in
         match uu____13599 with
         | (env_depth,()) ->
             let uu____13615 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____13615 with
              | (varops_depth,()) ->
                  let uu____13631 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____13631 with
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
        (fun uu____13674  ->
           let uu____13675 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____13675 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____13737 = snapshot msg  in () 
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
        | (uu____13778::uu____13779,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___119_13787 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___119_13787.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___119_13787.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___119_13787.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____13788 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____13807 =
        let uu____13810 =
          let uu____13811 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____13811  in
        let uu____13812 = open_fact_db_tags env  in uu____13810 ::
          uu____13812
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____13807
  
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
      let uu____13838 = encode_sigelt env se  in
      match uu____13838 with
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
        let uu____13882 = FStar_Options.log_queries ()  in
        if uu____13882
        then
          let uu____13885 =
            let uu____13886 =
              let uu____13887 =
                let uu____13888 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____13888 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____13887  in
            FStar_SMTEncoding_Term.Caption uu____13886  in
          uu____13885 :: decls
        else decls  in
      (let uu____13899 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13899
       then
         let uu____13900 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____13900
       else ());
      (let env =
         let uu____13903 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____13903 tcenv  in
       let uu____13904 = encode_top_level_facts env se  in
       match uu____13904 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____13918 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____13918)))
  
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
      (let uu____13934 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13934
       then
         let uu____13935 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____13935
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____13976  ->
                 fun se  ->
                   match uu____13976 with
                   | (g,env2) ->
                       let uu____13996 = encode_top_level_facts env2 se  in
                       (match uu____13996 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14019 =
         encode_signature
           (let uu___120_14028 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___120_14028.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___120_14028.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___120_14028.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___120_14028.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___120_14028.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___120_14028.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___120_14028.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___120_14028.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___120_14028.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___120_14028.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14019 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14047 = FStar_Options.log_queries ()  in
             if uu____14047
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___121_14055 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___121_14055.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___121_14055.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___121_14055.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___121_14055.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___121_14055.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___121_14055.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___121_14055.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___121_14055.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___121_14055.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___121_14055.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14057 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14057
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
        (let uu____14115 =
           let uu____14116 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14116.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14115);
        (let env =
           let uu____14118 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14118 tcenv  in
         let uu____14119 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____14158 = aux rest  in
                 (match uu____14158 with
                  | (out,rest1) ->
                      let t =
                        let uu____14186 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14186 with
                        | FStar_Pervasives_Native.Some uu____14189 ->
                            let uu____14190 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14190
                              x.FStar_Syntax_Syntax.sort
                        | uu____14191 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14195 =
                        let uu____14198 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___122_14201 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___122_14201.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___122_14201.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14198 :: out  in
                      (uu____14195, rest1))
             | uu____14206 -> ([], bindings)  in
           let uu____14213 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____14213 with
           | (closing,bindings) ->
               let uu____14240 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14240, bindings)
            in
         match uu____14119 with
         | (q1,bindings) ->
             let uu____14271 = encode_env_bindings env bindings  in
             (match uu____14271 with
              | (env_decls,env1) ->
                  ((let uu____14293 =
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
                    if uu____14293
                    then
                      let uu____14294 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14294
                    else ());
                   (let uu____14296 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14296 with
                    | (phi,qdecls) ->
                        let uu____14317 =
                          let uu____14322 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14322 phi
                           in
                        (match uu____14317 with
                         | (labels,phi1) ->
                             let uu____14339 = encode_labels labels  in
                             (match uu____14339 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14376 =
                                      let uu____14383 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14384 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14383,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14384)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14376
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
  