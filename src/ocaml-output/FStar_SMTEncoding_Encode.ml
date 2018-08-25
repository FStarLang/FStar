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
                                  (let uu___375_4712 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___375_4712.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___375_4712.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___375_4712.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___375_4712.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___375_4712.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___375_4712.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___375_4712.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___375_4712.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___375_4712.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___375_4712.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___375_4712.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___375_4712.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___375_4712.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___375_4712.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___375_4712.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___375_4712.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___375_4712.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___375_4712.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___375_4712.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___375_4712.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___375_4712.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___375_4712.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___375_4712.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___375_4712.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___375_4712.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___375_4712.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___375_4712.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___375_4712.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___375_4712.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___375_4712.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___375_4712.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___375_4712.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___375_4712.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___375_4712.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___375_4712.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___375_4712.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___375_4712.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___375_4712.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___375_4712.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___375_4712.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___375_4712.FStar_TypeChecker_Env.nbe)
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
                                    (fun uu___365_4897  ->
                                       match uu___365_4897 with
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
                                             let uu___376_5211 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___376_5211.FStar_SMTEncoding_Env.encoding_quantifier)
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
                                                         (fun _0_17  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_17)
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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5591 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5591 with
          | FStar_Pervasives_Native.None  ->
              let uu____5602 = encode_free_var false env x t t_norm []  in
              (match uu____5602 with
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
            let uu____5669 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5669 with
            | (decls,env1) ->
                let uu____5688 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5688
                then
                  let uu____5695 =
                    let uu____5698 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5698  in
                  (uu____5695, env1)
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
             (fun uu____5756  ->
                fun lb  ->
                  match uu____5756 with
                  | (decls,env1) ->
                      let uu____5776 =
                        let uu____5783 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5783
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5776 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5806 = FStar_Syntax_Util.head_and_args t  in
    match uu____5806 with
    | (hd1,args) ->
        let uu____5849 =
          let uu____5850 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5850.FStar_Syntax_Syntax.n  in
        (match uu____5849 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5854,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5877 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5883 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___377_5889 = en  in
    let uu____5890 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___377_5889.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___377_5889.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___377_5889.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___377_5889.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___377_5889.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____5890;
      FStar_SMTEncoding_Env.nolabels =
        (uu___377_5889.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___377_5889.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___377_5889.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___377_5889.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___377_5889.FStar_SMTEncoding_Env.encoding_quantifier)
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
    fun uu____5920  ->
      fun quals  ->
        match uu____5920 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____6024 = FStar_Util.first_N nbinders formals  in
              match uu____6024 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6125  ->
                         fun uu____6126  ->
                           match (uu____6125, uu____6126) with
                           | ((formal,uu____6152),(binder,uu____6154)) ->
                               let uu____6175 =
                                 let uu____6182 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6182)  in
                               FStar_Syntax_Syntax.NT uu____6175) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6196 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6237  ->
                              match uu____6237 with
                              | (x,i) ->
                                  let uu____6256 =
                                    let uu___378_6257 = x  in
                                    let uu____6258 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___378_6257.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___378_6257.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6258
                                    }  in
                                  (uu____6256, i)))
                       in
                    FStar_All.pipe_right uu____6196
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6282 =
                      let uu____6287 = FStar_Syntax_Subst.compress body  in
                      let uu____6288 =
                        let uu____6289 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6289
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6287 uu____6288
                       in
                    uu____6282 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6372 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6372
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___379_6377 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___379_6377.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___379_6377.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___379_6377.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___379_6377.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___379_6377.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___379_6377.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___379_6377.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___379_6377.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___379_6377.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___379_6377.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___379_6377.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___379_6377.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___379_6377.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___379_6377.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___379_6377.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___379_6377.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___379_6377.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___379_6377.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___379_6377.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___379_6377.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___379_6377.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___379_6377.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___379_6377.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___379_6377.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___379_6377.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___379_6377.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___379_6377.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___379_6377.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___379_6377.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___379_6377.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___379_6377.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___379_6377.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___379_6377.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___379_6377.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___379_6377.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___379_6377.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___379_6377.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___379_6377.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___379_6377.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___379_6377.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___379_6377.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6422 = FStar_Syntax_Util.abs_formals e  in
                match uu____6422 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6502::uu____6503 ->
                         let uu____6524 =
                           let uu____6525 =
                             let uu____6528 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6528
                              in
                           uu____6525.FStar_Syntax_Syntax.n  in
                         (match uu____6524 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6585 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6585 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6641 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6641
                                   then
                                     let uu____6684 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6684 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6804  ->
                                                   fun uu____6805  ->
                                                     match (uu____6804,
                                                             uu____6805)
                                                     with
                                                     | ((x,uu____6831),
                                                        (b,uu____6833)) ->
                                                         let uu____6854 =
                                                           let uu____6861 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6861)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6854)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6869 =
                                            let uu____6898 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6898)  in
                                          (uu____6869, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6992 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6992 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____7159) ->
                              let uu____7164 =
                                let uu____7193 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____7193  in
                              (uu____7164, true)
                          | uu____7282 when Prims.op_Negation norm1 ->
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
                          | uu____7284 ->
                              let uu____7285 =
                                let uu____7286 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____7287 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____7286 uu____7287
                                 in
                              failwith uu____7285)
                     | uu____7320 ->
                         let rec aux' t_norm2 =
                           let uu____7359 =
                             let uu____7360 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____7360.FStar_Syntax_Syntax.n  in
                           match uu____7359 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____7417 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____7417 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____7459 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____7459 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7583) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7588 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___381_7657  ->
                  match () with
                  | () ->
                      let uu____7664 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____7664
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____7676 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____7739  ->
                                   fun lb  ->
                                     match uu____7739 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____7794 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____7794
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____7797 =
                                             let uu____7806 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____7806
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____7797 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____7676 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____7932 =
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
                               | uu____7938 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____7946 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____7946 vars)
                                   else
                                     (let uu____7948 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____7948)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____8008;
                                    FStar_Syntax_Syntax.lbeff = uu____8009;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8011;
                                    FStar_Syntax_Syntax.lbpos = uu____8012;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8036 =
                                     let uu____8045 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8045 with
                                     | (tcenv',uu____8063,e_t) ->
                                         let uu____8069 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8086 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8069 with
                                          | (e1,t_norm1) ->
                                              ((let uu___382_8112 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___382_8112.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8036 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8126 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____8126 with
                                         | ((binders,body,uu____8147,t_body),curry)
                                             ->
                                             ((let uu____8159 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8159
                                               then
                                                 let uu____8160 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8161 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8160 uu____8161
                                               else ());
                                              (let uu____8163 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8163 with
                                               | (vars,guards,env'1,binder_decls,uu____8190)
                                                   ->
                                                   let body1 =
                                                     let uu____8204 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8204
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
                                                     let uu____8225 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____8225 curry
                                                       fvb vars
                                                      in
                                                   let uu____8226 =
                                                     let is_logical =
                                                       let uu____8238 =
                                                         let uu____8239 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____8239.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____8238 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____8243 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____8245 =
                                                         let uu____8246 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____8246
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____8245
                                                         (fun lid  ->
                                                            let uu____8254 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____8254
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____8255 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____8255
                                                     then
                                                       let uu____8268 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____8269 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____8268,
                                                         uu____8269)
                                                     else
                                                       (let uu____8279 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____8279))
                                                      in
                                                   (match uu____8226 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____8303 =
                                                            let uu____8310 =
                                                              let uu____8311
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8312
                                                                =
                                                                let uu____8323
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____8323)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8311
                                                                uu____8312
                                                               in
                                                            let uu____8332 =
                                                              let uu____8333
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8333
                                                               in
                                                            (uu____8310,
                                                              uu____8332,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8303
                                                           in
                                                        let uu____8334 =
                                                          let uu____8337 =
                                                            let uu____8340 =
                                                              let uu____8343
                                                                =
                                                                let uu____8346
                                                                  =
                                                                  primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1
                                                                   in
                                                                FStar_List.append
                                                                  [eqn]
                                                                  uu____8346
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____8343
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____8340
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____8337
                                                           in
                                                        (uu____8334, env2))))))
                               | uu____8351 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____8414 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____8414,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____8417 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____8464  ->
                                         fun fvb  ->
                                           match uu____8464 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____8510 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8510
                                                  in
                                               let gtok =
                                                 let uu____8512 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8512
                                                  in
                                               let env4 =
                                                 let uu____8514 =
                                                   let uu____8517 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_18  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_18) uu____8517
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____8514
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____8417 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____8623
                                     t_norm uu____8625 =
                                     match (uu____8623, uu____8625) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____8653;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____8654;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____8656;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____8657;_})
                                         ->
                                         let uu____8678 =
                                           let uu____8687 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____8687 with
                                           | (tcenv',uu____8705,e_t) ->
                                               let uu____8711 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____8728 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____8711 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___383_8754 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___383_8754.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____8678 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____8773 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____8773
                                                then
                                                  let uu____8774 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____8775 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____8776 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____8774 uu____8775
                                                    uu____8776
                                                else ());
                                               (let uu____8778 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____8778 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____8815 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____8815
                                                      then
                                                        let uu____8816 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____8817 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____8818 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____8819 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____8816
                                                          uu____8817
                                                          uu____8818
                                                          uu____8819
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____8823 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____8823 with
                                                      | (vars,guards,env'1,binder_decls,uu____8854)
                                                          ->
                                                          let decl_g =
                                                            let uu____8868 =
                                                              let uu____8879
                                                                =
                                                                let uu____8882
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____8882
                                                                 in
                                                              (g, uu____8879,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____8868
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
                                                            let uu____8895 =
                                                              let uu____8902
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____8902)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____8895
                                                             in
                                                          let gsapp =
                                                            let uu____8908 =
                                                              let uu____8915
                                                                =
                                                                let uu____8918
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____8918 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____8915)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____8908
                                                             in
                                                          let gmax =
                                                            let uu____8924 =
                                                              let uu____8931
                                                                =
                                                                let uu____8934
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____8934 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____8931)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____8924
                                                             in
                                                          let body1 =
                                                            let uu____8940 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____8940
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____8942 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____8942
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____8960
                                                                   =
                                                                   let uu____8967
                                                                    =
                                                                    let uu____8968
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8969
                                                                    =
                                                                    let uu____8984
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
                                                                    uu____8984)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____8968
                                                                    uu____8969
                                                                     in
                                                                   let uu____8995
                                                                    =
                                                                    let uu____8996
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8996
                                                                     in
                                                                   (uu____8967,
                                                                    uu____8995,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____8960
                                                                  in
                                                               let eqn_f =
                                                                 let uu____8998
                                                                   =
                                                                   let uu____9005
                                                                    =
                                                                    let uu____9006
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9007
                                                                    =
                                                                    let uu____9018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9018)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9006
                                                                    uu____9007
                                                                     in
                                                                   (uu____9005,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____8998
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____9028
                                                                   =
                                                                   let uu____9035
                                                                    =
                                                                    let uu____9036
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9037
                                                                    =
                                                                    let uu____9048
                                                                    =
                                                                    let uu____9049
                                                                    =
                                                                    let uu____9054
                                                                    =
                                                                    let uu____9055
                                                                    =
                                                                    let uu____9062
                                                                    =
                                                                    let uu____9065
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9065
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____9062)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____9055
                                                                     in
                                                                    (gsapp,
                                                                    uu____9054)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9049
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9048)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9036
                                                                    uu____9037
                                                                     in
                                                                   (uu____9035,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____9028
                                                                  in
                                                               let uu____9076
                                                                 =
                                                                 let uu____9085
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____9085
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____9114)
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
                                                                    let uu____9135
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9135
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____9136
                                                                    =
                                                                    let uu____9143
                                                                    =
                                                                    let uu____9144
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9145
                                                                    =
                                                                    let uu____9156
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____9156)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9144
                                                                    uu____9145
                                                                     in
                                                                    (uu____9143,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9136
                                                                     in
                                                                    let uu____9165
                                                                    =
                                                                    let uu____9174
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____9174
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____9189
                                                                    =
                                                                    let uu____9192
                                                                    =
                                                                    let uu____9193
                                                                    =
                                                                    let uu____9200
                                                                    =
                                                                    let uu____9201
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9202
                                                                    =
                                                                    let uu____9213
                                                                    =
                                                                    let uu____9214
                                                                    =
                                                                    let uu____9219
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____9219,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9214
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____9213)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9201
                                                                    uu____9202
                                                                     in
                                                                    (uu____9200,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9193
                                                                     in
                                                                    [uu____9192]
                                                                     in
                                                                    (d3,
                                                                    uu____9189)
                                                                     in
                                                                    (match uu____9165
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
                                                               (match uu____9076
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
                                   let uu____9278 =
                                     let uu____9291 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____9348  ->
                                          fun uu____9349  ->
                                            match (uu____9348, uu____9349)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____9464 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____9464 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____9291
                                      in
                                   (match uu____9278 with
                                    | (decls2,eqns,env01) ->
                                        let uu____9537 =
                                          let isDeclFun uu___366_9551 =
                                            match uu___366_9551 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____9552 -> true
                                            | uu____9563 -> false  in
                                          let uu____9564 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____9564
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____9537 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____9604 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___367_9608  ->
                                        match uu___367_9608 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____9609 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____9615 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____9615)))
                                in
                             if uu____9604
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___385_9632  ->
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
                   let uu____9667 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9667
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
        let uu____9728 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9728 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9732 = encode_sigelt' env se  in
      match uu____9732 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9744 =
                  let uu____9745 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9745  in
                [uu____9744]
            | uu____9746 ->
                let uu____9747 =
                  let uu____9750 =
                    let uu____9751 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9751  in
                  uu____9750 :: g  in
                let uu____9752 =
                  let uu____9755 =
                    let uu____9756 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9756  in
                  [uu____9755]  in
                FStar_List.append uu____9747 uu____9752
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
        let uu____9769 =
          let uu____9770 = FStar_Syntax_Subst.compress t  in
          uu____9770.FStar_Syntax_Syntax.n  in
        match uu____9769 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9774)) -> s = "opaque_to_smt"
        | uu____9775 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9782 =
          let uu____9783 = FStar_Syntax_Subst.compress t  in
          uu____9783.FStar_Syntax_Syntax.n  in
        match uu____9782 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9787)) -> s = "uninterpreted_by_smt"
        | uu____9788 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9793 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9798 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9809 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9810 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9811 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9824 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9826 =
            let uu____9827 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____9827  in
          if uu____9826
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9853 ->
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
               let uu____9885 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9885 with
               | (formals,uu____9905) ->
                   let arity = FStar_List.length formals  in
                   let uu____9929 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9929 with
                    | (aname,atok,env2) ->
                        let uu____9949 =
                          let uu____9954 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9954
                            env2
                           in
                        (match uu____9949 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9966 =
                                 let uu____9967 =
                                   let uu____9978 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9998  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9978,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9967
                                  in
                               [uu____9966;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____10009 =
                               let aux uu____10067 uu____10068 =
                                 match (uu____10067, uu____10068) with
                                 | ((bv,uu____10124),(env3,acc_sorts,acc)) ->
                                     let uu____10168 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____10168 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____10009 with
                              | (uu____10242,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____10265 =
                                      let uu____10272 =
                                        let uu____10273 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10274 =
                                          let uu____10285 =
                                            let uu____10286 =
                                              let uu____10291 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____10291)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____10286
                                             in
                                          ([[app]], xs_sorts, uu____10285)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10273 uu____10274
                                         in
                                      (uu____10272,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10265
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
                                    let uu____10303 =
                                      let uu____10310 =
                                        let uu____10311 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10312 =
                                          let uu____10323 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____10323)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10311 uu____10312
                                         in
                                      (uu____10310,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10303
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____10334 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____10334 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____10360,uu____10361)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____10362 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____10362 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____10377,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____10383 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___368_10387  ->
                      match uu___368_10387 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____10388 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____10393 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10394 -> false))
               in
            Prims.op_Negation uu____10383  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____10401 =
               let uu____10408 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____10408 env fv t quals  in
             match uu____10401 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____10423 =
                   let uu____10424 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____10424  in
                 (uu____10423, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____10430 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____10430 with
           | (uvs,f1) ->
               let env1 =
                 let uu___386_10442 = env  in
                 let uu____10443 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___386_10442.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___386_10442.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___386_10442.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____10443;
                   FStar_SMTEncoding_Env.warn =
                     (uu___386_10442.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___386_10442.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___386_10442.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___386_10442.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___386_10442.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___386_10442.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___386_10442.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____10445 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____10445 with
                | (f3,decls) ->
                    let g =
                      let uu____10459 =
                        let uu____10460 =
                          let uu____10467 =
                            let uu____10468 =
                              let uu____10469 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____10469
                               in
                            FStar_Pervasives_Native.Some uu____10468  in
                          let uu____10470 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____10467, uu____10470)  in
                        FStar_SMTEncoding_Util.mkAssume uu____10460  in
                      [uu____10459]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10472) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____10484 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____10506 =
                       let uu____10509 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____10509.FStar_Syntax_Syntax.fv_name  in
                     uu____10506.FStar_Syntax_Syntax.v  in
                   let uu____10510 =
                     let uu____10511 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____10511  in
                   if uu____10510
                   then
                     let val_decl =
                       let uu___387_10541 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___387_10541.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___387_10541.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___387_10541.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10542 = encode_sigelt' env1 val_decl  in
                     match uu____10542 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____10484 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10576,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10578;
                          FStar_Syntax_Syntax.lbtyp = uu____10579;
                          FStar_Syntax_Syntax.lbeff = uu____10580;
                          FStar_Syntax_Syntax.lbdef = uu____10581;
                          FStar_Syntax_Syntax.lbattrs = uu____10582;
                          FStar_Syntax_Syntax.lbpos = uu____10583;_}::[]),uu____10584)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10601 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10601 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10630 =
                   let uu____10633 =
                     let uu____10634 =
                       let uu____10641 =
                         let uu____10642 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10643 =
                           let uu____10654 =
                             let uu____10655 =
                               let uu____10660 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10660)  in
                             FStar_SMTEncoding_Util.mkEq uu____10655  in
                           ([[b2t_x]], [xx], uu____10654)  in
                         FStar_SMTEncoding_Term.mkForall uu____10642
                           uu____10643
                          in
                       (uu____10641,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10634  in
                   [uu____10633]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10630
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10681,uu____10682) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___369_10691  ->
                  match uu___369_10691 with
                  | FStar_Syntax_Syntax.Discriminator uu____10692 -> true
                  | uu____10693 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10694,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10705 =
                     let uu____10706 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10706.FStar_Ident.idText  in
                   uu____10705 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___370_10710  ->
                     match uu___370_10710 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10711 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10713) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___371_10724  ->
                  match uu___371_10724 with
                  | FStar_Syntax_Syntax.Projector uu____10725 -> true
                  | uu____10730 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10733 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10733 with
           | FStar_Pervasives_Native.Some uu____10740 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___388_10742 = se  in
                 let uu____10743 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10743;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___388_10742.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___388_10742.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___388_10742.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10746) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10758) ->
          let uu____10767 = encode_sigelts env ses  in
          (match uu____10767 with
           | (g,env1) ->
               let uu____10784 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___372_10807  ->
                         match uu___372_10807 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10808;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10809;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10810;_}
                             -> false
                         | uu____10813 -> true))
                  in
               (match uu____10784 with
                | (g',inversions) ->
                    let uu____10828 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___373_10849  ->
                              match uu___373_10849 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10850 ->
                                  true
                              | uu____10861 -> false))
                       in
                    (match uu____10828 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10877,tps,k,uu____10880,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___374_10897  ->
                    match uu___374_10897 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10898 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10909 = c  in
              match uu____10909 with
              | (name,args,uu____10914,uu____10915,uu____10916) ->
                  let uu____10921 =
                    let uu____10922 =
                      let uu____10933 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10956  ->
                                match uu____10956 with
                                | (uu____10963,sort,uu____10965) -> sort))
                         in
                      (name, uu____10933, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10922  in
                  [uu____10921]
            else
              (let uu____10969 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____10969 c)
             in
          let inversion_axioms tapp vars =
            let uu____10995 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____11001 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____11001 FStar_Option.isNone))
               in
            if uu____10995
            then []
            else
              (let uu____11033 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____11033 with
               | (xxsym,xx) ->
                   let uu____11042 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____11081  ->
                             fun l  ->
                               match uu____11081 with
                               | (out,decls) ->
                                   let uu____11101 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____11101 with
                                    | (uu____11112,data_t) ->
                                        let uu____11114 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____11114 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____11158 =
                                                 let uu____11159 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____11159.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____11158 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____11162,indices) ->
                                                   indices
                                               | uu____11188 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____11218  ->
                                                         match uu____11218
                                                         with
                                                         | (x,uu____11226) ->
                                                             let uu____11231
                                                               =
                                                               let uu____11232
                                                                 =
                                                                 let uu____11239
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____11239,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____11232
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____11231)
                                                    env)
                                                in
                                             let uu____11242 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____11242 with
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
                                                      let uu____11268 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____11284
                                                                 =
                                                                 let uu____11289
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____11289,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____11284)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____11268
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____11292 =
                                                      let uu____11293 =
                                                        let uu____11298 =
                                                          let uu____11299 =
                                                            let uu____11304 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____11304,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____11299
                                                           in
                                                        (out, uu____11298)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____11293
                                                       in
                                                    (uu____11292,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____11042 with
                    | (data_ax,decls) ->
                        let uu____11317 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____11317 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____11328 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____11328 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____11332 =
                                 let uu____11339 =
                                   let uu____11340 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____11341 =
                                     let uu____11352 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____11361 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____11352,
                                       uu____11361)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____11340 uu____11341
                                    in
                                 let uu____11370 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____11339,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____11370)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____11332
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____11371 =
            let uu____11376 =
              let uu____11377 = FStar_Syntax_Subst.compress k  in
              uu____11377.FStar_Syntax_Syntax.n  in
            match uu____11376 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____11412 -> (tps, k)  in
          (match uu____11371 with
           | (formals,res) ->
               let uu____11419 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11419 with
                | (formals1,res1) ->
                    let uu____11430 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____11430 with
                     | (vars,guards,env',binder_decls,uu____11455) ->
                         let arity = FStar_List.length vars  in
                         let uu____11469 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11469 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11492 =
                                  let uu____11499 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11499)  in
                                FStar_SMTEncoding_Util.mkApp uu____11492  in
                              let uu____11504 =
                                let tname_decl =
                                  let uu____11514 =
                                    let uu____11515 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11539  ->
                                              match uu____11539 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11552 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11515,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11552, false)
                                     in
                                  constructor_or_logic_type_decl uu____11514
                                   in
                                let uu____11555 =
                                  match vars with
                                  | [] ->
                                      let uu____11568 =
                                        let uu____11569 =
                                          let uu____11572 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_19  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_19) uu____11572
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11569
                                         in
                                      ([], uu____11568)
                                  | uu____11583 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11590 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11590
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11604 =
                                          let uu____11611 =
                                            let uu____11612 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____11613 =
                                              let uu____11628 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11628)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____11612 uu____11613
                                             in
                                          (uu____11611,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11604
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11555 with
                                | (tok_decls,env2) ->
                                    let uu____11649 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____11649
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____11504 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11674 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11674 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11694 =
                                               let uu____11695 =
                                                 let uu____11702 =
                                                   let uu____11703 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11703
                                                    in
                                                 (uu____11702,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11695
                                                in
                                             [uu____11694]
                                           else []  in
                                         let uu____11705 =
                                           let uu____11708 =
                                             let uu____11711 =
                                               let uu____11712 =
                                                 let uu____11719 =
                                                   let uu____11720 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11721 =
                                                     let uu____11732 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11732)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11720 uu____11721
                                                    in
                                                 (uu____11719,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11712
                                                in
                                             [uu____11711]  in
                                           FStar_List.append karr uu____11708
                                            in
                                         FStar_List.append decls1 uu____11705
                                      in
                                   let aux =
                                     let uu____11744 =
                                       let uu____11747 =
                                         inversion_axioms tapp vars  in
                                       let uu____11750 =
                                         let uu____11753 =
                                           let uu____11754 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11754 env2
                                             tapp vars
                                            in
                                         [uu____11753]  in
                                       FStar_List.append uu____11747
                                         uu____11750
                                        in
                                     FStar_List.append kindingAx uu____11744
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11759,uu____11760,uu____11761,uu____11762,uu____11763)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11769,t,uu____11771,n_tps,uu____11773) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11781 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11781 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11829 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11829 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11850 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11850 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11864 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11864 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11934 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11934,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11938 =
                                  let uu____11939 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11939, true)
                                   in
                                let uu____11942 =
                                  let uu____11949 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____11949
                                   in
                                FStar_All.pipe_right uu____11938 uu____11942
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
                              let uu____11960 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11960 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11972::uu____11973 ->
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
                                         let uu____12018 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____12019 =
                                           let uu____12030 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____12030)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12018 uu____12019
                                     | uu____12049 -> tok_typing  in
                                   let uu____12058 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____12058 with
                                    | (vars',guards',env'',decls_formals,uu____12083)
                                        ->
                                        let uu____12096 =
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
                                        (match uu____12096 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____12125 ->
                                                   let uu____12134 =
                                                     let uu____12135 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____12135
                                                      in
                                                   [uu____12134]
                                                in
                                             let encode_elim uu____12149 =
                                               let uu____12150 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____12150 with
                                               | (head1,args) ->
                                                   let uu____12201 =
                                                     let uu____12202 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____12202.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____12201 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____12214;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____12215;_},uu____12216)
                                                        ->
                                                        let uu____12221 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12221
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12236
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12236
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
                                                                    uu____12287
                                                                    ->
                                                                    let uu____12288
                                                                    =
                                                                    let uu____12293
                                                                    =
                                                                    let uu____12294
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12294
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12293)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12288
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12310
                                                                    =
                                                                    let uu____12311
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12311
                                                                     in
                                                                    if
                                                                    uu____12310
                                                                    then
                                                                    let uu____12324
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12324]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12326
                                                                    =
                                                                    let uu____12339
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12395
                                                                     ->
                                                                    fun
                                                                    uu____12396
                                                                     ->
                                                                    match 
                                                                    (uu____12395,
                                                                    uu____12396)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12501
                                                                    =
                                                                    let uu____12508
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12508
                                                                     in
                                                                    (match uu____12501
                                                                    with
                                                                    | 
                                                                    (uu____12521,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12529
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12529
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12533
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12533
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
                                                                    uu____12339
                                                                     in
                                                                  (match uu____12326
                                                                   with
                                                                   | 
                                                                   (uu____12550,arg_vars,elim_eqns_or_guards,uu____12553)
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
                                                                    let uu____12577
                                                                    =
                                                                    let uu____12584
                                                                    =
                                                                    let uu____12585
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12586
                                                                    =
                                                                    let uu____12597
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12598
                                                                    =
                                                                    let uu____12599
                                                                    =
                                                                    let uu____12604
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12604)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12599
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12597,
                                                                    uu____12598)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12585
                                                                    uu____12586
                                                                     in
                                                                    (uu____12584,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12577
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12615
                                                                    =
                                                                    let uu____12620
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12620,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12615
                                                                     in
                                                                    let uu____12621
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12621
                                                                    then
                                                                    let x =
                                                                    let uu____12627
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12627,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12629
                                                                    =
                                                                    let uu____12636
                                                                    =
                                                                    let uu____12637
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12638
                                                                    =
                                                                    let uu____12649
                                                                    =
                                                                    let uu____12654
                                                                    =
                                                                    let uu____12657
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12657]
                                                                     in
                                                                    [uu____12654]
                                                                     in
                                                                    let uu____12662
                                                                    =
                                                                    let uu____12663
                                                                    =
                                                                    let uu____12668
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12669
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12668,
                                                                    uu____12669)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12663
                                                                     in
                                                                    (uu____12649,
                                                                    [x],
                                                                    uu____12662)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12637
                                                                    uu____12638
                                                                     in
                                                                    let uu____12682
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12636,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12682)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12629
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12687
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
                                                                    (let uu____12719
                                                                    =
                                                                    let uu____12720
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12720
                                                                    dapp1  in
                                                                    [uu____12719])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12687
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12727
                                                                    =
                                                                    let uu____12734
                                                                    =
                                                                    let uu____12735
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12736
                                                                    =
                                                                    let uu____12747
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12748
                                                                    =
                                                                    let uu____12749
                                                                    =
                                                                    let uu____12754
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12754)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12749
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12747,
                                                                    uu____12748)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12735
                                                                    uu____12736
                                                                     in
                                                                    (uu____12734,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12727)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12768 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12768
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12783
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12783
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
                                                                    uu____12834
                                                                    ->
                                                                    let uu____12835
                                                                    =
                                                                    let uu____12840
                                                                    =
                                                                    let uu____12841
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12841
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12840)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12835
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12857
                                                                    =
                                                                    let uu____12858
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12858
                                                                     in
                                                                    if
                                                                    uu____12857
                                                                    then
                                                                    let uu____12871
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12871]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12873
                                                                    =
                                                                    let uu____12886
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12942
                                                                     ->
                                                                    fun
                                                                    uu____12943
                                                                     ->
                                                                    match 
                                                                    (uu____12942,
                                                                    uu____12943)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13048
                                                                    =
                                                                    let uu____13055
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13055
                                                                     in
                                                                    (match uu____13048
                                                                    with
                                                                    | 
                                                                    (uu____13068,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13076
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13076
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13080
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13080
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
                                                                    uu____12886
                                                                     in
                                                                  (match uu____12873
                                                                   with
                                                                   | 
                                                                   (uu____13097,arg_vars,elim_eqns_or_guards,uu____13100)
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
                                                                    let uu____13124
                                                                    =
                                                                    let uu____13131
                                                                    =
                                                                    let uu____13132
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13133
                                                                    =
                                                                    let uu____13144
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13145
                                                                    =
                                                                    let uu____13146
                                                                    =
                                                                    let uu____13151
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13151)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13146
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13144,
                                                                    uu____13145)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13132
                                                                    uu____13133
                                                                     in
                                                                    (uu____13131,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13124
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13162
                                                                    =
                                                                    let uu____13167
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13167,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13162
                                                                     in
                                                                    let uu____13168
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13168
                                                                    then
                                                                    let x =
                                                                    let uu____13174
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13174,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13176
                                                                    =
                                                                    let uu____13183
                                                                    =
                                                                    let uu____13184
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13185
                                                                    =
                                                                    let uu____13196
                                                                    =
                                                                    let uu____13201
                                                                    =
                                                                    let uu____13204
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13204]
                                                                     in
                                                                    [uu____13201]
                                                                     in
                                                                    let uu____13209
                                                                    =
                                                                    let uu____13210
                                                                    =
                                                                    let uu____13215
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13216
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13215,
                                                                    uu____13216)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13210
                                                                     in
                                                                    (uu____13196,
                                                                    [x],
                                                                    uu____13209)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13184
                                                                    uu____13185
                                                                     in
                                                                    let uu____13229
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13183,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13229)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13176
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13234
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
                                                                    (let uu____13266
                                                                    =
                                                                    let uu____13267
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____13267
                                                                    dapp1  in
                                                                    [uu____13266])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13234
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____13274
                                                                    =
                                                                    let uu____13281
                                                                    =
                                                                    let uu____13282
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13283
                                                                    =
                                                                    let uu____13294
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13295
                                                                    =
                                                                    let uu____13296
                                                                    =
                                                                    let uu____13301
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____13301)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13296
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13294,
                                                                    uu____13295)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13282
                                                                    uu____13283
                                                                     in
                                                                    (uu____13281,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13274)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____13314 ->
                                                        ((let uu____13316 =
                                                            let uu____13321 =
                                                              let uu____13322
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____13323
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____13322
                                                                uu____13323
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____13321)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____13316);
                                                         ([], [])))
                                                in
                                             let uu____13328 = encode_elim ()
                                                in
                                             (match uu____13328 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____13354 =
                                                      let uu____13357 =
                                                        let uu____13360 =
                                                          let uu____13363 =
                                                            let uu____13366 =
                                                              let uu____13367
                                                                =
                                                                let uu____13378
                                                                  =
                                                                  let uu____13379
                                                                    =
                                                                    let uu____13380
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____13380
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____13379
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____13378)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____13367
                                                               in
                                                            [uu____13366]  in
                                                          let uu____13383 =
                                                            let uu____13386 =
                                                              let uu____13389
                                                                =
                                                                let uu____13392
                                                                  =
                                                                  let uu____13395
                                                                    =
                                                                    let uu____13398
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____13399
                                                                    =
                                                                    let uu____13402
                                                                    =
                                                                    let uu____13403
                                                                    =
                                                                    let uu____13410
                                                                    =
                                                                    let uu____13411
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13412
                                                                    =
                                                                    let uu____13423
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____13423)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13411
                                                                    uu____13412
                                                                     in
                                                                    (uu____13410,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13403
                                                                     in
                                                                    let uu____13432
                                                                    =
                                                                    let uu____13435
                                                                    =
                                                                    let uu____13436
                                                                    =
                                                                    let uu____13443
                                                                    =
                                                                    let uu____13444
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13445
                                                                    =
                                                                    let uu____13456
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____13457
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____13456,
                                                                    uu____13457)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13444
                                                                    uu____13445
                                                                     in
                                                                    (uu____13443,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13436
                                                                     in
                                                                    [uu____13435]
                                                                     in
                                                                    uu____13402
                                                                    ::
                                                                    uu____13432
                                                                     in
                                                                    uu____13398
                                                                    ::
                                                                    uu____13399
                                                                     in
                                                                  FStar_List.append
                                                                    uu____13395
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____13392
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____13389
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____13386
                                                             in
                                                          FStar_List.append
                                                            uu____13363
                                                            uu____13383
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____13360
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____13357
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____13354
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
           (fun uu____13491  ->
              fun se  ->
                match uu____13491 with
                | (g,env1) ->
                    let uu____13511 = encode_sigelt env1 se  in
                    (match uu____13511 with
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
      let encode_binding b uu____13576 =
        match uu____13576 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____13608 ->
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
                 ((let uu____13614 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13614
                   then
                     let uu____13615 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13616 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13617 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13615 uu____13616 uu____13617
                   else ());
                  (let uu____13619 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13619 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13635 =
                         let uu____13642 =
                           let uu____13643 =
                             let uu____13644 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13644
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13643  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13642
                          in
                       (match uu____13635 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13658 = FStar_Options.log_queries ()
                                 in
                              if uu____13658
                              then
                                let uu____13659 =
                                  let uu____13660 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13661 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13662 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13660 uu____13661 uu____13662
                                   in
                                FStar_Pervasives_Native.Some uu____13659
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____13674,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13694 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13694 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13717 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13717 with | (uu____13740,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13753 'Auu____13754 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13753,'Auu____13754)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13823  ->
              match uu____13823 with
              | (l,uu____13835,uu____13836) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13880  ->
              match uu____13880 with
              | (l,uu____13894,uu____13895) ->
                  let uu____13904 =
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_SMTEncoding_Term.Echo _0_20)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13905 =
                    let uu____13908 =
                      let uu____13909 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13909  in
                    [uu____13908]  in
                  uu____13904 :: uu____13905))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13936 =
      let uu____13939 =
        let uu____13940 = FStar_Util.psmap_empty ()  in
        let uu____13955 = FStar_Util.psmap_empty ()  in
        let uu____13958 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13961 =
          let uu____13962 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13962 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13940;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13955;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13958;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13961;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13939]  in
    FStar_ST.op_Colon_Equals last_env uu____13936
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13996 = FStar_ST.op_Bang last_env  in
      match uu____13996 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14023 ->
          let uu___389_14026 = e  in
          let uu____14027 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___389_14026.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___389_14026.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___389_14026.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___389_14026.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___389_14026.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___389_14026.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___389_14026.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___389_14026.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____14027;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___389_14026.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____14033 = FStar_ST.op_Bang last_env  in
    match uu____14033 with
    | [] -> failwith "Empty env stack"
    | uu____14059::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____14090  ->
    let uu____14091 = FStar_ST.op_Bang last_env  in
    match uu____14091 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____14149  ->
    let uu____14150 = FStar_ST.op_Bang last_env  in
    match uu____14150 with
    | [] -> failwith "Popping an empty stack"
    | uu____14176::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____14211  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____14254  ->
         let uu____14255 = snapshot_env ()  in
         match uu____14255 with
         | (env_depth,()) ->
             let uu____14271 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____14271 with
              | (varops_depth,()) ->
                  let uu____14287 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____14287 with
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
        (fun uu____14330  ->
           let uu____14331 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____14331 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____14393 = snapshot msg  in () 
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
        | (uu____14434::uu____14435,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___390_14443 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___390_14443.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___390_14443.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___390_14443.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____14444 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____14463 =
        let uu____14466 =
          let uu____14467 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____14467  in
        let uu____14468 = open_fact_db_tags env  in uu____14466 ::
          uu____14468
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____14463
  
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
      let uu____14494 = encode_sigelt env se  in
      match uu____14494 with
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
        let uu____14538 = FStar_Options.log_queries ()  in
        if uu____14538
        then
          let uu____14541 =
            let uu____14542 =
              let uu____14543 =
                let uu____14544 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14544 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14543  in
            FStar_SMTEncoding_Term.Caption uu____14542  in
          uu____14541 :: decls
        else decls  in
      (let uu____14555 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14555
       then
         let uu____14556 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14556
       else ());
      (let env =
         let uu____14559 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14559 tcenv  in
       let uu____14560 = encode_top_level_facts env se  in
       match uu____14560 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14574 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14574)))
  
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
      (let uu____14590 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14590
       then
         let uu____14591 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14591
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14632  ->
                 fun se  ->
                   match uu____14632 with
                   | (g,env2) ->
                       let uu____14652 = encode_top_level_facts env2 se  in
                       (match uu____14652 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14675 =
         encode_signature
           (let uu___391_14684 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___391_14684.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___391_14684.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___391_14684.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___391_14684.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___391_14684.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___391_14684.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___391_14684.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___391_14684.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___391_14684.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___391_14684.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14675 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14703 = FStar_Options.log_queries ()  in
             if uu____14703
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___392_14711 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___392_14711.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___392_14711.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___392_14711.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___392_14711.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___392_14711.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___392_14711.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___392_14711.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___392_14711.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___392_14711.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___392_14711.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14713 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14713
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
        (let uu____14771 =
           let uu____14772 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14772.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14771);
        (let env =
           let uu____14774 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14774 tcenv  in
         let uu____14775 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____14814 = aux rest  in
                 (match uu____14814 with
                  | (out,rest1) ->
                      let t =
                        let uu____14842 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14842 with
                        | FStar_Pervasives_Native.Some uu____14845 ->
                            let uu____14846 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14846
                              x.FStar_Syntax_Syntax.sort
                        | uu____14847 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14851 =
                        let uu____14854 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___393_14857 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___393_14857.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___393_14857.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14854 :: out  in
                      (uu____14851, rest1))
             | uu____14862 -> ([], bindings)  in
           let uu____14869 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____14869 with
           | (closing,bindings) ->
               let uu____14896 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14896, bindings)
            in
         match uu____14775 with
         | (q1,bindings) ->
             let uu____14927 = encode_env_bindings env bindings  in
             (match uu____14927 with
              | (env_decls,env1) ->
                  ((let uu____14949 =
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
                    if uu____14949
                    then
                      let uu____14950 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14950
                    else ());
                   (let uu____14952 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14952 with
                    | (phi,qdecls) ->
                        let uu____14973 =
                          let uu____14978 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14978 phi
                           in
                        (match uu____14973 with
                         | (labels,phi1) ->
                             let uu____14995 = encode_labels labels  in
                             (match uu____14995 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15032 =
                                      let uu____15039 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15040 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____15039,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____15040)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15032
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
  