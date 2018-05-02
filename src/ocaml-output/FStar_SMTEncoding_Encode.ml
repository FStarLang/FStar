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
                    let uu____231 =
                      let uu____238 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____238)  in
                    FStar_SMTEncoding_Util.mkApp uu____231  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____251 =
                    let uu____254 =
                      let uu____257 =
                        let uu____260 =
                          let uu____261 =
                            let uu____268 =
                              let uu____269 =
                                let uu____280 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____280)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____269
                               in
                            (uu____268, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____261  in
                        let uu____297 =
                          let uu____300 =
                            let uu____301 =
                              let uu____308 =
                                let uu____309 =
                                  let uu____320 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____320)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____309
                                 in
                              (uu____308,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____301  in
                          [uu____300]  in
                        uu____260 :: uu____297  in
                      xtok_decl :: uu____257  in
                    xname_decl :: uu____254  in
                  (xtok1, (FStar_List.length vars), uu____251)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____421 =
                    let uu____440 =
                      let uu____457 =
                        let uu____458 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____458
                         in
                      quant axy uu____457  in
                    (FStar_Parser_Const.op_Eq, uu____440)  in
                  let uu____473 =
                    let uu____494 =
                      let uu____513 =
                        let uu____530 =
                          let uu____531 =
                            let uu____532 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____532  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____531
                           in
                        quant axy uu____530  in
                      (FStar_Parser_Const.op_notEq, uu____513)  in
                    let uu____547 =
                      let uu____568 =
                        let uu____587 =
                          let uu____604 =
                            let uu____605 =
                              let uu____606 =
                                let uu____611 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____612 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____611, uu____612)  in
                              FStar_SMTEncoding_Util.mkLT uu____606  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____605
                             in
                          quant xy uu____604  in
                        (FStar_Parser_Const.op_LT, uu____587)  in
                      let uu____627 =
                        let uu____648 =
                          let uu____667 =
                            let uu____684 =
                              let uu____685 =
                                let uu____686 =
                                  let uu____691 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____692 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____691, uu____692)  in
                                FStar_SMTEncoding_Util.mkLTE uu____686  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____685
                               in
                            quant xy uu____684  in
                          (FStar_Parser_Const.op_LTE, uu____667)  in
                        let uu____707 =
                          let uu____728 =
                            let uu____747 =
                              let uu____764 =
                                let uu____765 =
                                  let uu____766 =
                                    let uu____771 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____772 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____771, uu____772)  in
                                  FStar_SMTEncoding_Util.mkGT uu____766  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____765
                                 in
                              quant xy uu____764  in
                            (FStar_Parser_Const.op_GT, uu____747)  in
                          let uu____787 =
                            let uu____808 =
                              let uu____827 =
                                let uu____844 =
                                  let uu____845 =
                                    let uu____846 =
                                      let uu____851 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____852 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____851, uu____852)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____846
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____845
                                   in
                                quant xy uu____844  in
                              (FStar_Parser_Const.op_GTE, uu____827)  in
                            let uu____867 =
                              let uu____888 =
                                let uu____907 =
                                  let uu____924 =
                                    let uu____925 =
                                      let uu____926 =
                                        let uu____931 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____932 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____931, uu____932)  in
                                      FStar_SMTEncoding_Util.mkSub uu____926
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____925
                                     in
                                  quant xy uu____924  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____907)
                                 in
                              let uu____947 =
                                let uu____968 =
                                  let uu____987 =
                                    let uu____1004 =
                                      let uu____1005 =
                                        let uu____1006 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1006
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1005
                                       in
                                    quant qx uu____1004  in
                                  (FStar_Parser_Const.op_Minus, uu____987)
                                   in
                                let uu____1021 =
                                  let uu____1042 =
                                    let uu____1061 =
                                      let uu____1078 =
                                        let uu____1079 =
                                          let uu____1080 =
                                            let uu____1085 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1086 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1085, uu____1086)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1080
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1079
                                         in
                                      quant xy uu____1078  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1061)
                                     in
                                  let uu____1101 =
                                    let uu____1122 =
                                      let uu____1141 =
                                        let uu____1158 =
                                          let uu____1159 =
                                            let uu____1160 =
                                              let uu____1165 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1166 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1165, uu____1166)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1160
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1159
                                           in
                                        quant xy uu____1158  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1141)
                                       in
                                    let uu____1181 =
                                      let uu____1202 =
                                        let uu____1221 =
                                          let uu____1238 =
                                            let uu____1239 =
                                              let uu____1240 =
                                                let uu____1245 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1246 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1245, uu____1246)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1240
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1239
                                             in
                                          quant xy uu____1238  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1221)
                                         in
                                      let uu____1261 =
                                        let uu____1282 =
                                          let uu____1301 =
                                            let uu____1318 =
                                              let uu____1319 =
                                                let uu____1320 =
                                                  let uu____1325 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1326 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1325, uu____1326)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1320
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1319
                                               in
                                            quant xy uu____1318  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1301)
                                           in
                                        let uu____1341 =
                                          let uu____1362 =
                                            let uu____1381 =
                                              let uu____1398 =
                                                let uu____1399 =
                                                  let uu____1400 =
                                                    let uu____1405 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1406 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1405, uu____1406)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1400
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1399
                                                 in
                                              quant xy uu____1398  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1381)
                                             in
                                          let uu____1421 =
                                            let uu____1442 =
                                              let uu____1461 =
                                                let uu____1478 =
                                                  let uu____1479 =
                                                    let uu____1480 =
                                                      let uu____1485 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1486 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1485,
                                                        uu____1486)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1480
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1479
                                                   in
                                                quant xy uu____1478  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1461)
                                               in
                                            let uu____1501 =
                                              let uu____1522 =
                                                let uu____1541 =
                                                  let uu____1558 =
                                                    let uu____1559 =
                                                      let uu____1560 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1560
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1559
                                                     in
                                                  quant qx uu____1558  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1541)
                                                 in
                                              [uu____1522]  in
                                            uu____1442 :: uu____1501  in
                                          uu____1362 :: uu____1421  in
                                        uu____1282 :: uu____1341  in
                                      uu____1202 :: uu____1261  in
                                    uu____1122 :: uu____1181  in
                                  uu____1042 :: uu____1101  in
                                uu____968 :: uu____1021  in
                              uu____888 :: uu____947  in
                            uu____808 :: uu____867  in
                          uu____728 :: uu____787  in
                        uu____648 :: uu____707  in
                      uu____568 :: uu____627  in
                    uu____494 :: uu____547  in
                  uu____421 :: uu____473  in
                let mk1 l v1 =
                  let uu____1882 =
                    let uu____1893 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1975  ->
                              match uu____1975 with
                              | (l',uu____1993) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____1893
                      (FStar_Option.map
                         (fun uu____2082  ->
                            match uu____2082 with
                            | (uu____2107,b) ->
                                let uu____2137 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2137 v1))
                     in
                  FStar_All.pipe_right uu____1882 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2211  ->
                          match uu____2211 with
                          | (l',uu____2229) -> FStar_Ident.lid_equals l l'))
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
          let uu____2290 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2290 with
          | (xxsym,xx) ->
              let uu____2297 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2297 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2307 =
                     let uu____2314 =
                       let uu____2315 =
                         let uu____2326 =
                           let uu____2327 =
                             let uu____2332 =
                               let uu____2333 =
                                 let uu____2338 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2338)  in
                               FStar_SMTEncoding_Util.mkEq uu____2333  in
                             (xx_has_type, uu____2332)  in
                           FStar_SMTEncoding_Util.mkImp uu____2327  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2326)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2315  in
                     let uu____2363 =
                       let uu____2364 =
                         let uu____2365 =
                           let uu____2366 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2366  in
                         Prims.strcat module_name uu____2365  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2364
                        in
                     (uu____2314, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2363)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2307)
  
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
    let uu____2416 =
      let uu____2417 =
        let uu____2424 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2424, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2417  in
    let uu____2427 =
      let uu____2430 =
        let uu____2431 =
          let uu____2438 =
            let uu____2439 =
              let uu____2450 =
                let uu____2451 =
                  let uu____2456 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2456)  in
                FStar_SMTEncoding_Util.mkImp uu____2451  in
              ([[typing_pred]], [xx], uu____2450)  in
            let uu____2479 =
              let uu____2494 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2494  in
            uu____2479 uu____2439  in
          (uu____2438, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2431  in
      [uu____2430]  in
    uu____2416 :: uu____2427  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2520 =
      let uu____2521 =
        let uu____2528 =
          let uu____2529 = FStar_TypeChecker_Env.get_range env  in
          let uu____2530 =
            let uu____2541 =
              let uu____2546 =
                let uu____2549 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2549]  in
              [uu____2546]  in
            let uu____2554 =
              let uu____2555 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2555 tt  in
            (uu____2541, [bb], uu____2554)  in
          FStar_SMTEncoding_Term.mkForall uu____2529 uu____2530  in
        (uu____2528, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2521  in
    let uu____2576 =
      let uu____2579 =
        let uu____2580 =
          let uu____2587 =
            let uu____2588 =
              let uu____2599 =
                let uu____2600 =
                  let uu____2605 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2605)  in
                FStar_SMTEncoding_Util.mkImp uu____2600  in
              ([[typing_pred]], [xx], uu____2599)  in
            let uu____2628 =
              let uu____2643 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2643  in
            uu____2628 uu____2588  in
          (uu____2587, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2580  in
      [uu____2579]  in
    uu____2520 :: uu____2576  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____2663 =
        let uu____2668 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____2668, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____2663  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____2684 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2684  in
    let uu____2687 =
      let uu____2688 =
        let uu____2695 =
          let uu____2696 = FStar_TypeChecker_Env.get_range env  in
          let uu____2697 =
            let uu____2708 =
              let uu____2713 =
                let uu____2716 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2716]  in
              [uu____2713]  in
            let uu____2721 =
              let uu____2722 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2722 tt  in
            (uu____2708, [bb], uu____2721)  in
          FStar_SMTEncoding_Term.mkForall uu____2696 uu____2697  in
        (uu____2695, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2688  in
    let uu____2743 =
      let uu____2746 =
        let uu____2747 =
          let uu____2754 =
            let uu____2755 =
              let uu____2766 =
                let uu____2767 =
                  let uu____2772 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2772)  in
                FStar_SMTEncoding_Util.mkImp uu____2767  in
              ([[typing_pred]], [xx], uu____2766)  in
            let uu____2795 =
              let uu____2810 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2810  in
            uu____2795 uu____2755  in
          (uu____2754, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2747  in
      let uu____2813 =
        let uu____2816 =
          let uu____2817 =
            let uu____2824 =
              let uu____2825 =
                let uu____2836 =
                  let uu____2837 =
                    let uu____2842 =
                      let uu____2843 =
                        let uu____2846 =
                          let uu____2849 =
                            let uu____2852 =
                              let uu____2853 =
                                let uu____2858 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2859 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2858, uu____2859)  in
                              FStar_SMTEncoding_Util.mkGT uu____2853  in
                            let uu____2860 =
                              let uu____2863 =
                                let uu____2864 =
                                  let uu____2869 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2870 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2869, uu____2870)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2864  in
                              let uu____2871 =
                                let uu____2874 =
                                  let uu____2875 =
                                    let uu____2880 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2881 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2880, uu____2881)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2875  in
                                [uu____2874]  in
                              uu____2863 :: uu____2871  in
                            uu____2852 :: uu____2860  in
                          typing_pred_y :: uu____2849  in
                        typing_pred :: uu____2846  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2843  in
                    (uu____2842, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2837  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2836)
                 in
              let uu____2908 =
                let uu____2923 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2923  in
              uu____2908 uu____2825  in
            (uu____2824,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2817  in
        [uu____2816]  in
      uu____2746 :: uu____2813  in
    uu____2687 :: uu____2743  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2949 =
      let uu____2950 =
        let uu____2957 =
          let uu____2958 = FStar_TypeChecker_Env.get_range env  in
          let uu____2959 =
            let uu____2970 =
              let uu____2975 =
                let uu____2978 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2978]  in
              [uu____2975]  in
            let uu____2983 =
              let uu____2984 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2984 tt  in
            (uu____2970, [bb], uu____2983)  in
          FStar_SMTEncoding_Term.mkForall uu____2958 uu____2959  in
        (uu____2957, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2950  in
    let uu____3005 =
      let uu____3008 =
        let uu____3009 =
          let uu____3016 =
            let uu____3017 =
              let uu____3028 =
                let uu____3029 =
                  let uu____3034 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3034)  in
                FStar_SMTEncoding_Util.mkImp uu____3029  in
              ([[typing_pred]], [xx], uu____3028)  in
            let uu____3057 =
              let uu____3072 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3072  in
            uu____3057 uu____3017  in
          (uu____3016, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3009  in
      [uu____3008]  in
    uu____2949 :: uu____3005  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3115 =
      let uu____3116 =
        let uu____3123 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3123, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3116  in
    [uu____3115]  in
  let mk_and_interp env conj uu____3141 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3166 =
      let uu____3167 =
        let uu____3174 =
          let uu____3175 = FStar_TypeChecker_Env.get_range env  in
          let uu____3176 =
            let uu____3187 =
              let uu____3188 =
                let uu____3193 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3193, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3188  in
            ([[l_and_a_b]], [aa; bb], uu____3187)  in
          FStar_SMTEncoding_Term.mkForall uu____3175 uu____3176  in
        (uu____3174, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3167  in
    [uu____3166]  in
  let mk_or_interp env disj uu____3237 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3262 =
      let uu____3263 =
        let uu____3270 =
          let uu____3271 = FStar_TypeChecker_Env.get_range env  in
          let uu____3272 =
            let uu____3283 =
              let uu____3284 =
                let uu____3289 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3289, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3284  in
            ([[l_or_a_b]], [aa; bb], uu____3283)  in
          FStar_SMTEncoding_Term.mkForall uu____3271 uu____3272  in
        (uu____3270, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3263  in
    [uu____3262]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3358 =
      let uu____3359 =
        let uu____3366 =
          let uu____3367 = FStar_TypeChecker_Env.get_range env  in
          let uu____3368 =
            let uu____3379 =
              let uu____3380 =
                let uu____3385 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3385, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3380  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3379)  in
          FStar_SMTEncoding_Term.mkForall uu____3367 uu____3368  in
        (uu____3366, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3359  in
    [uu____3358]  in
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
    let uu____3464 =
      let uu____3465 =
        let uu____3472 =
          let uu____3473 = FStar_TypeChecker_Env.get_range env  in
          let uu____3474 =
            let uu____3485 =
              let uu____3486 =
                let uu____3491 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3491, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3486  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3485)  in
          FStar_SMTEncoding_Term.mkForall uu____3473 uu____3474  in
        (uu____3472, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3465  in
    [uu____3464]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3568 =
      let uu____3569 =
        let uu____3576 =
          let uu____3577 = FStar_TypeChecker_Env.get_range env  in
          let uu____3578 =
            let uu____3589 =
              let uu____3590 =
                let uu____3595 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3595, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3590  in
            ([[l_imp_a_b]], [aa; bb], uu____3589)  in
          FStar_SMTEncoding_Term.mkForall uu____3577 uu____3578  in
        (uu____3576, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3569  in
    [uu____3568]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3664 =
      let uu____3665 =
        let uu____3672 =
          let uu____3673 = FStar_TypeChecker_Env.get_range env  in
          let uu____3674 =
            let uu____3685 =
              let uu____3686 =
                let uu____3691 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3691, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3686  in
            ([[l_iff_a_b]], [aa; bb], uu____3685)  in
          FStar_SMTEncoding_Term.mkForall uu____3673 uu____3674  in
        (uu____3672, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3665  in
    [uu____3664]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3749 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3749  in
    let uu____3752 =
      let uu____3753 =
        let uu____3760 =
          let uu____3761 = FStar_TypeChecker_Env.get_range env  in
          let uu____3762 =
            let uu____3773 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3773)  in
          FStar_SMTEncoding_Term.mkForall uu____3761 uu____3762  in
        (uu____3760, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3753  in
    [uu____3752]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3817 =
      let uu____3818 =
        let uu____3825 =
          let uu____3826 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3826 range_ty  in
        let uu____3827 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3825, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3827)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3818  in
    [uu____3817]  in
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
        let uu____3867 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3867 x1 t  in
      let uu____3868 = FStar_TypeChecker_Env.get_range env  in
      let uu____3869 =
        let uu____3880 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3880)  in
      FStar_SMTEncoding_Term.mkForall uu____3868 uu____3869  in
    let uu____3903 =
      let uu____3904 =
        let uu____3911 =
          let uu____3912 = FStar_TypeChecker_Env.get_range env  in
          let uu____3913 =
            let uu____3924 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3924)  in
          FStar_SMTEncoding_Term.mkForall uu____3912 uu____3913  in
        (uu____3911,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3904  in
    [uu____3903]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3980 =
      let uu____3981 =
        let uu____3988 =
          let uu____3989 = FStar_TypeChecker_Env.get_range env  in
          let uu____3990 =
            let uu____4005 =
              let uu____4006 =
                let uu____4011 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4012 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4011, uu____4012)  in
              FStar_SMTEncoding_Util.mkAnd uu____4006  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4005)
             in
          FStar_SMTEncoding_Term.mkForall' uu____3989 uu____3990  in
        (uu____3988,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3981  in
    [uu____3980]  in
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
          let uu____4428 =
            FStar_Util.find_opt
              (fun uu____4460  ->
                 match uu____4460 with
                 | (l,uu____4472) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4428 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4506,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4557 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4557 with
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
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
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
              let uu____4609 =
                ((let uu____4612 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4612) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4609
              then
                let arg_sorts =
                  let uu____4622 =
                    let uu____4623 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4623.FStar_Syntax_Syntax.n  in
                  match uu____4622 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4629) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4659  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4664 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4666 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4666 with
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
                (let uu____4699 = prims.is lid  in
                 if uu____4699
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4707 = prims.mk lid vname  in
                   match uu____4707 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4734 =
                      let uu____4745 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4745 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4763 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4763
                            then
                              let uu____4764 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___105_4767 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___105_4767.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___105_4767.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___105_4767.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___105_4767.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___105_4767.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___105_4767.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___105_4767.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___105_4767.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___105_4767.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___105_4767.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___105_4767.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___105_4767.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___105_4767.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___105_4767.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___105_4767.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___105_4767.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___105_4767.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___105_4767.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___105_4767.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___105_4767.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___105_4767.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___105_4767.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___105_4767.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___105_4767.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___105_4767.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___105_4767.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___105_4767.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___105_4767.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___105_4767.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___105_4767.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___105_4767.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___105_4767.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___105_4767.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___105_4767.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___105_4767.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___105_4767.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4764
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4779 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4779)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4734 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4829 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4829 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4854 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___94_4904  ->
                                       match uu___94_4904 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4908 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4908 with
                                            | (uu____4929,(xxsym,uu____4931))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4949 =
                                                  let uu____4950 =
                                                    let uu____4957 =
                                                      let uu____4958 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4959 =
                                                        let uu____4970 =
                                                          let uu____4971 =
                                                            let uu____4976 =
                                                              let uu____4977
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4977
                                                               in
                                                            (vapp,
                                                              uu____4976)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4971
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4970)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4958 uu____4959
                                                       in
                                                    (uu____4957,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4950
                                                   in
                                                [uu____4949])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4996 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4996 with
                                            | (uu____5017,(xxsym,uu____5019))
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
                                                let uu____5042 =
                                                  let uu____5043 =
                                                    let uu____5050 =
                                                      let uu____5051 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5052 =
                                                        let uu____5063 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5063)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5051 uu____5052
                                                       in
                                                    (uu____5050,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5043
                                                   in
                                                [uu____5042])
                                       | uu____5080 -> []))
                                in
                             let uu____5081 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5081 with
                              | (vars,guards,env',decls1,uu____5108) ->
                                  let uu____5121 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5130 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5130, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5132 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5132 with
                                         | (g,ds) ->
                                             let uu____5143 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5143,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5121 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5156 =
                                           let uu____5163 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5163)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5156
                                          in
                                       let uu____5172 =
                                         let vname_decl =
                                           let uu____5180 =
                                             let uu____5191 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5201  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5191,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5180
                                            in
                                         let uu____5210 =
                                           let env2 =
                                             let uu___106_5216 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___106_5216.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____5217 =
                                             let uu____5218 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5218  in
                                           if uu____5217
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5210 with
                                         | (tok_typing,decls2) ->
                                             let uu____5232 =
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
                                                   let uu____5252 =
                                                     let uu____5253 =
                                                       let uu____5256 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_17  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_17)
                                                         uu____5256
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____5253
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____5252)
                                               | uu____5265 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____5272 =
                                                       let uu____5279 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____5279]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____5272
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____5286 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____5287 =
                                                       let uu____5298 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____5298)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____5286 uu____5287
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5310 =
                                                       let uu____5317 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____5317,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5310
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
                                                       let uu____5346 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5347 =
                                                         let uu____5358 =
                                                           let uu____5359 =
                                                             let uu____5364 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____5365 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____5364,
                                                               uu____5365)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____5359
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____5358)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5346
                                                         uu____5347
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
                                             (match uu____5232 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5172 with
                                        | (decls2,env2) ->
                                            let uu____5418 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5426 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5426 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5439 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5439,
                                                    decls)
                                               in
                                            (match uu____5418 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5450 =
                                                     let uu____5457 =
                                                       let uu____5458 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5459 =
                                                         let uu____5470 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5470)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5458
                                                         uu____5459
                                                        in
                                                     (uu____5457,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5450
                                                    in
                                                 let freshness =
                                                   let uu____5486 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5486
                                                   then
                                                     let uu____5491 =
                                                       let uu____5492 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5493 =
                                                         let uu____5504 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5515 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5504,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5515)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5492
                                                         uu____5493
                                                        in
                                                     let uu____5518 =
                                                       let uu____5521 =
                                                         let uu____5522 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5522 env2
                                                           vapp vars
                                                          in
                                                       [uu____5521]  in
                                                     uu____5491 :: uu____5518
                                                   else []  in
                                                 let g =
                                                   let uu____5527 =
                                                     let uu____5530 =
                                                       let uu____5533 =
                                                         let uu____5536 =
                                                           let uu____5539 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5539
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5536
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5533
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5530
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5527
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5572 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5572 with
          | FStar_Pervasives_Native.None  ->
              let uu____5583 = encode_free_var false env x t t_norm []  in
              (match uu____5583 with
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
        FStar_Syntax_Syntax.term ->
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
            let uu____5646 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5646 with
            | (decls,env1) ->
                let uu____5665 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5665
                then
                  let uu____5672 =
                    let uu____5675 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5675  in
                  (uu____5672, env1)
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
             (fun uu____5733  ->
                fun lb  ->
                  match uu____5733 with
                  | (decls,env1) ->
                      let uu____5753 =
                        let uu____5760 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5760
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5753 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5783 = FStar_Syntax_Util.head_and_args t  in
    match uu____5783 with
    | (hd1,args) ->
        let uu____5820 =
          let uu____5821 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5821.FStar_Syntax_Syntax.n  in
        (match uu____5820 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5825,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5844 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5850 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5878  ->
      fun quals  ->
        match uu____5878 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5962 = FStar_Util.first_N nbinders formals  in
              match uu____5962 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6043  ->
                         fun uu____6044  ->
                           match (uu____6043, uu____6044) with
                           | ((formal,uu____6062),(binder,uu____6064)) ->
                               let uu____6073 =
                                 let uu____6080 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6080)  in
                               FStar_Syntax_Syntax.NT uu____6073) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6088 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6119  ->
                              match uu____6119 with
                              | (x,i) ->
                                  let uu____6130 =
                                    let uu___107_6131 = x  in
                                    let uu____6132 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___107_6131.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___107_6131.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6132
                                    }  in
                                  (uu____6130, i)))
                       in
                    FStar_All.pipe_right uu____6088
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6150 =
                      let uu____6155 = FStar_Syntax_Subst.compress body  in
                      let uu____6156 =
                        let uu____6157 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6157
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6155 uu____6156
                       in
                    uu____6150 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6226 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6226
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___108_6229 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___108_6229.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___108_6229.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___108_6229.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___108_6229.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___108_6229.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___108_6229.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___108_6229.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___108_6229.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___108_6229.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___108_6229.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___108_6229.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___108_6229.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___108_6229.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___108_6229.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___108_6229.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___108_6229.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___108_6229.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___108_6229.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___108_6229.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___108_6229.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___108_6229.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___108_6229.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___108_6229.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___108_6229.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___108_6229.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___108_6229.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___108_6229.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___108_6229.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___108_6229.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___108_6229.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___108_6229.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___108_6229.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___108_6229.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___108_6229.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___108_6229.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___108_6229.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6266 = FStar_Syntax_Util.abs_formals e  in
                match uu____6266 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6330::uu____6331 ->
                         let uu____6346 =
                           let uu____6347 =
                             let uu____6350 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6350
                              in
                           uu____6347.FStar_Syntax_Syntax.n  in
                         (match uu____6346 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6393 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6393 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6435 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6435
                                   then
                                     let uu____6470 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6470 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6564  ->
                                                   fun uu____6565  ->
                                                     match (uu____6564,
                                                             uu____6565)
                                                     with
                                                     | ((x,uu____6583),
                                                        (b,uu____6585)) ->
                                                         let uu____6594 =
                                                           let uu____6601 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6601)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6594)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6603 =
                                            let uu____6624 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6624)  in
                                          (uu____6603, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6692 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6692 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6781) ->
                              let uu____6786 =
                                let uu____6807 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6807  in
                              (uu____6786, true)
                          | uu____6872 when Prims.op_Negation norm1 ->
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
                          | uu____6874 ->
                              let uu____6875 =
                                let uu____6876 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6877 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6876 uu____6877
                                 in
                              failwith uu____6875)
                     | uu____6902 ->
                         let rec aux' t_norm2 =
                           let uu____6929 =
                             let uu____6930 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6930.FStar_Syntax_Syntax.n  in
                           match uu____6929 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6971 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6971 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____6999 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____6999 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7079) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7084 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____7140 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____7140
               then encode_top_level_vals env bindings quals
               else
                 (let uu____7152 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____7215  ->
                            fun lb  ->
                              match uu____7215 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____7270 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____7270
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____7273 =
                                      let uu____7282 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____7282
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____7273 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____7152 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7407 =
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
                        | uu____7413 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7421 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7421 vars)
                            else
                              (let uu____7423 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7423)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7483;
                             FStar_Syntax_Syntax.lbeff = uu____7484;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7486;
                             FStar_Syntax_Syntax.lbpos = uu____7487;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7511 =
                              let uu____7518 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7518 with
                              | (tcenv',uu____7536,e_t) ->
                                  let uu____7542 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7553 -> failwith "Impossible"  in
                                  (match uu____7542 with
                                   | (e1,t_norm1) ->
                                       ((let uu___111_7569 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___111_7569.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___111_7569.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___111_7569.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___111_7569.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___111_7569.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____7511 with
                             | (env',e1,t_norm1) ->
                                 let uu____7579 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7579 with
                                  | ((binders,body,uu____7600,t_body),curry)
                                      ->
                                      ((let uu____7612 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7612
                                        then
                                          let uu____7613 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7614 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7613 uu____7614
                                        else ());
                                       (let uu____7616 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7616 with
                                        | (vars,guards,env'1,binder_decls,uu____7643)
                                            ->
                                            let body1 =
                                              let uu____7657 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7657
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
                                              let uu____7674 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7674 curry fvb
                                                vars
                                               in
                                            let uu____7675 =
                                              let uu____7684 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7684
                                              then
                                                let uu____7695 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7696 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7695, uu____7696)
                                              else
                                                (let uu____7706 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7706))
                                               in
                                            (match uu____7675 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7729 =
                                                     let uu____7736 =
                                                       let uu____7737 =
                                                         FStar_Syntax_Util.range_of_lbname
                                                           lbn
                                                          in
                                                       let uu____7738 =
                                                         let uu____7749 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7749)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7737
                                                         uu____7738
                                                        in
                                                     let uu____7760 =
                                                       let uu____7763 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7763
                                                        in
                                                     (uu____7736, uu____7760,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7729
                                                    in
                                                 let uu____7766 =
                                                   let uu____7769 =
                                                     let uu____7772 =
                                                       let uu____7775 =
                                                         let uu____7778 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7778
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7775
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7772
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7769
                                                    in
                                                 (uu____7766, env2))))))
                        | uu____7783 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7846 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7846, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7849 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7896  ->
                                  fun fvb  ->
                                    match uu____7896 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7942 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7942
                                           in
                                        let gtok =
                                          let uu____7944 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7944
                                           in
                                        let env4 =
                                          let uu____7946 =
                                            let uu____7949 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_18  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_18) uu____7949
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7946
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7849 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____8057 t_norm
                              uu____8059 =
                              match (uu____8057, uu____8059) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____8089;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____8090;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____8092;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____8093;_})
                                  ->
                                  let uu____8114 =
                                    let uu____8121 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____8121 with
                                    | (tcenv',uu____8143,e_t) ->
                                        let uu____8149 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____8160 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____8149 with
                                         | (e1,t_norm1) ->
                                             ((let uu___112_8176 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___112_8176.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____8114 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____8191 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____8191
                                         then
                                           let uu____8192 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____8193 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____8194 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____8192 uu____8193 uu____8194
                                         else ());
                                        (let uu____8196 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____8196 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____8233 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8233
                                               then
                                                 let uu____8234 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8235 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8236 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____8237 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____8234 uu____8235
                                                   uu____8236 uu____8237
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____8241 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8241 with
                                               | (vars,guards,env'1,binder_decls,uu____8272)
                                                   ->
                                                   let decl_g =
                                                     let uu____8286 =
                                                       let uu____8297 =
                                                         let uu____8300 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____8300
                                                          in
                                                       (g, uu____8297,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____8286
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
                                                     let uu____8325 =
                                                       let uu____8332 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____8332)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8325
                                                      in
                                                   let gsapp =
                                                     let uu____8342 =
                                                       let uu____8349 =
                                                         let uu____8352 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____8352 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8349)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8342
                                                      in
                                                   let gmax =
                                                     let uu____8358 =
                                                       let uu____8365 =
                                                         let uu____8368 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____8368 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8365)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8358
                                                      in
                                                   let body1 =
                                                     let uu____8374 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8374
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____8376 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____8376 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8394 =
                                                            let uu____8401 =
                                                              let uu____8402
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8403
                                                                =
                                                                let uu____8418
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
                                                                  uu____8418)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall'
                                                                uu____8402
                                                                uu____8403
                                                               in
                                                            let uu____8439 =
                                                              let uu____8442
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8442
                                                               in
                                                            (uu____8401,
                                                              uu____8439,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8394
                                                           in
                                                        let eqn_f =
                                                          let uu____8446 =
                                                            let uu____8453 =
                                                              let uu____8454
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8455
                                                                =
                                                                let uu____8466
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8466)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8454
                                                                uu____8455
                                                               in
                                                            (uu____8453,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8446
                                                           in
                                                        let eqn_g' =
                                                          let uu____8480 =
                                                            let uu____8487 =
                                                              let uu____8488
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8489
                                                                =
                                                                let uu____8500
                                                                  =
                                                                  let uu____8501
                                                                    =
                                                                    let uu____8506
                                                                    =
                                                                    let uu____8507
                                                                    =
                                                                    let uu____8514
                                                                    =
                                                                    let uu____8517
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8517
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8514)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8507
                                                                     in
                                                                    (gsapp,
                                                                    uu____8506)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8501
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8500)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8488
                                                                uu____8489
                                                               in
                                                            (uu____8487,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8480
                                                           in
                                                        let uu____8540 =
                                                          let uu____8549 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8549
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8578)
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
                                                                  let uu____8603
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8603
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8608
                                                                  =
                                                                  let uu____8615
                                                                    =
                                                                    let uu____8616
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8617
                                                                    =
                                                                    let uu____8628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8628)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8616
                                                                    uu____8617
                                                                     in
                                                                  (uu____8615,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8608
                                                                 in
                                                              let uu____8649
                                                                =
                                                                let uu____8656
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8656
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8669
                                                                    =
                                                                    let uu____8672
                                                                    =
                                                                    let uu____8673
                                                                    =
                                                                    let uu____8680
                                                                    =
                                                                    let uu____8681
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8682
                                                                    =
                                                                    let uu____8693
                                                                    =
                                                                    let uu____8694
                                                                    =
                                                                    let uu____8699
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8699,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8694
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8693)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8681
                                                                    uu____8682
                                                                     in
                                                                    (uu____8680,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8673
                                                                     in
                                                                    [uu____8672]
                                                                     in
                                                                    (d3,
                                                                    uu____8669)
                                                                 in
                                                              (match uu____8649
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
                                                        (match uu____8540
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
                            let uu____8764 =
                              let uu____8777 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8838  ->
                                   fun uu____8839  ->
                                     match (uu____8838, uu____8839) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8964 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8964 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8777
                               in
                            (match uu____8764 with
                             | (decls2,eqns,env01) ->
                                 let uu____9037 =
                                   let isDeclFun uu___95_9051 =
                                     match uu___95_9051 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____9052 -> true
                                     | uu____9063 -> false  in
                                   let uu____9064 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____9064
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____9037 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____9104 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___96_9108  ->
                                 match uu___96_9108 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9109 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____9115 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____9115)))
                         in
                      if uu____9104
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
                   let uu____9167 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9167
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
        let uu____9228 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9228 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9232 = encode_sigelt' env se  in
      match uu____9232 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9248 =
                  let uu____9249 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9249  in
                [uu____9248]
            | uu____9250 ->
                let uu____9251 =
                  let uu____9254 =
                    let uu____9255 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9255  in
                  uu____9254 :: g  in
                let uu____9256 =
                  let uu____9259 =
                    let uu____9260 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9260  in
                  [uu____9259]  in
                FStar_List.append uu____9251 uu____9256
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
        let uu____9275 =
          let uu____9276 = FStar_Syntax_Subst.compress t  in
          uu____9276.FStar_Syntax_Syntax.n  in
        match uu____9275 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9280)) -> s = "opaque_to_smt"
        | uu____9281 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9288 =
          let uu____9289 = FStar_Syntax_Subst.compress t  in
          uu____9289.FStar_Syntax_Syntax.n  in
        match uu____9288 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9293)) -> s = "uninterpreted_by_smt"
        | uu____9294 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9299 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9304 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9315 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9318 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9321 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9336 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9340 =
            let uu____9341 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____9341 Prims.op_Negation  in
          if uu____9340
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9369 ->
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
               let uu____9393 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9393 with
               | (formals,uu____9411) ->
                   let arity = FStar_List.length formals  in
                   let uu____9429 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9429 with
                    | (aname,atok,env2) ->
                        let uu____9449 =
                          let uu____9454 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9454
                            env2
                           in
                        (match uu____9449 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9466 =
                                 let uu____9467 =
                                   let uu____9478 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9494  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9478,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9467
                                  in
                               [uu____9466;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9507 =
                               let aux uu____9563 uu____9564 =
                                 match (uu____9563, uu____9564) with
                                 | ((bv,uu____9616),(env3,acc_sorts,acc)) ->
                                     let uu____9654 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9654 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9507 with
                              | (uu____9726,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9749 =
                                      let uu____9756 =
                                        let uu____9757 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9758 =
                                          let uu____9769 =
                                            let uu____9770 =
                                              let uu____9775 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9775)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9770
                                             in
                                          ([[app]], xs_sorts, uu____9769)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9757 uu____9758
                                         in
                                      (uu____9756,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9749
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
                                    let uu____9795 =
                                      let uu____9802 =
                                        let uu____9803 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9804 =
                                          let uu____9815 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9815)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9803 uu____9804
                                         in
                                      (uu____9802,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9795
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9834 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9834 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9862,uu____9863) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9864 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9864 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9881,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9887 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___97_9891  ->
                      match uu___97_9891 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9892 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9897 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9898 -> false))
               in
            Prims.op_Negation uu____9887  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9907 =
               let uu____9914 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9914 env fv t quals  in
             match uu____9907 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9929 =
                   let uu____9932 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9932  in
                 (uu____9929, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9940 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9940 with
           | (uu____9949,f1) ->
               let uu____9951 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env  in
               (match uu____9951 with
                | (f2,decls) ->
                    let g =
                      let uu____9965 =
                        let uu____9966 =
                          let uu____9973 =
                            let uu____9976 =
                              let uu____9977 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9977
                               in
                            FStar_Pervasives_Native.Some uu____9976  in
                          let uu____9978 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____9973, uu____9978)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9966  in
                      [uu____9965]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9984) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____9996 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____10014 =
                       let uu____10017 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____10017.FStar_Syntax_Syntax.fv_name  in
                     uu____10014.FStar_Syntax_Syntax.v  in
                   let uu____10018 =
                     let uu____10019 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____10019  in
                   if uu____10018
                   then
                     let val_decl =
                       let uu___115_10047 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___115_10047.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___115_10047.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___115_10047.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10052 = encode_sigelt' env1 val_decl  in
                     match uu____10052 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____9996 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10080,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10082;
                          FStar_Syntax_Syntax.lbtyp = uu____10083;
                          FStar_Syntax_Syntax.lbeff = uu____10084;
                          FStar_Syntax_Syntax.lbdef = uu____10085;
                          FStar_Syntax_Syntax.lbattrs = uu____10086;
                          FStar_Syntax_Syntax.lbpos = uu____10087;_}::[]),uu____10088)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10111 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10111 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10140 =
                   let uu____10143 =
                     let uu____10144 =
                       let uu____10151 =
                         let uu____10152 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10153 =
                           let uu____10164 =
                             let uu____10165 =
                               let uu____10170 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10170)  in
                             FStar_SMTEncoding_Util.mkEq uu____10165  in
                           ([[b2t_x]], [xx], uu____10164)  in
                         FStar_SMTEncoding_Term.mkForall uu____10152
                           uu____10153
                          in
                       (uu____10151,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10144  in
                   [uu____10143]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10140
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10203,uu____10204) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___98_10213  ->
                  match uu___98_10213 with
                  | FStar_Syntax_Syntax.Discriminator uu____10214 -> true
                  | uu____10215 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10218,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10229 =
                     let uu____10230 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10230.FStar_Ident.idText  in
                   uu____10229 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___99_10234  ->
                     match uu___99_10234 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10235 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10239) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_10256  ->
                  match uu___100_10256 with
                  | FStar_Syntax_Syntax.Projector uu____10257 -> true
                  | uu____10262 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10265 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10265 with
           | FStar_Pervasives_Native.Some uu____10272 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___116_10276 = se  in
                 let uu____10277 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10277;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___116_10276.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___116_10276.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___116_10276.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10284) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10302) ->
          let uu____10311 = encode_sigelts env ses  in
          (match uu____10311 with
           | (g,env1) ->
               let uu____10328 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___101_10351  ->
                         match uu___101_10351 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10352;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10353;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10354;_}
                             -> false
                         | uu____10357 -> true))
                  in
               (match uu____10328 with
                | (g',inversions) ->
                    let uu____10372 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___102_10393  ->
                              match uu___102_10393 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10394 ->
                                  true
                              | uu____10405 -> false))
                       in
                    (match uu____10372 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10423,tps,k,uu____10426,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___103_10443  ->
                    match uu___103_10443 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10444 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10455 = c  in
              match uu____10455 with
              | (name,args,uu____10460,uu____10461,uu____10462) ->
                  let uu____10467 =
                    let uu____10468 =
                      let uu____10479 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10496  ->
                                match uu____10496 with
                                | (uu____10503,sort,uu____10505) -> sort))
                         in
                      (name, uu____10479, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10468  in
                  [uu____10467]
            else
              (let uu____10511 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____10511 c)
             in
          let inversion_axioms tapp vars =
            let uu____10537 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10543 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10543 FStar_Option.isNone))
               in
            if uu____10537
            then []
            else
              (let uu____10575 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10575 with
               | (xxsym,xx) ->
                   let uu____10584 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10623  ->
                             fun l  ->
                               match uu____10623 with
                               | (out,decls) ->
                                   let uu____10643 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10643 with
                                    | (uu____10654,data_t) ->
                                        let uu____10656 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10656 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10702 =
                                                 let uu____10703 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10703.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10702 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10714,indices) ->
                                                   indices
                                               | uu____10736 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10760  ->
                                                         match uu____10760
                                                         with
                                                         | (x,uu____10766) ->
                                                             let uu____10767
                                                               =
                                                               let uu____10768
                                                                 =
                                                                 let uu____10775
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10775,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10768
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10767)
                                                    env)
                                                in
                                             let uu____10778 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10778 with
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
                                                      let uu____10804 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10820
                                                                 =
                                                                 let uu____10825
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10825,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10820)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10804
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10828 =
                                                      let uu____10829 =
                                                        let uu____10834 =
                                                          let uu____10835 =
                                                            let uu____10840 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10840,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10835
                                                           in
                                                        (out, uu____10834)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10829
                                                       in
                                                    (uu____10828,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10584 with
                    | (data_ax,decls) ->
                        let uu____10853 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10853 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10864 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10864 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10868 =
                                 let uu____10875 =
                                   let uu____10876 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____10877 =
                                     let uu____10888 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10903 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10888,
                                       uu____10903)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____10876 uu____10877
                                    in
                                 let uu____10918 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10875,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10918)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10868
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10921 =
            let uu____10934 =
              let uu____10935 = FStar_Syntax_Subst.compress k  in
              uu____10935.FStar_Syntax_Syntax.n  in
            match uu____10934 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10980 -> (tps, k)  in
          (match uu____10921 with
           | (formals,res) ->
               let uu____11003 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11003 with
                | (formals1,res1) ->
                    let uu____11014 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____11014 with
                     | (vars,guards,env',binder_decls,uu____11039) ->
                         let arity = FStar_List.length vars  in
                         let uu____11053 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11053 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11076 =
                                  let uu____11083 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11083)  in
                                FStar_SMTEncoding_Util.mkApp uu____11076  in
                              let uu____11092 =
                                let tname_decl =
                                  let uu____11102 =
                                    let uu____11103 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11135  ->
                                              match uu____11135 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11148 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11103,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11148, false)
                                     in
                                  constructor_or_logic_type_decl uu____11102
                                   in
                                let uu____11157 =
                                  match vars with
                                  | [] ->
                                      let uu____11170 =
                                        let uu____11171 =
                                          let uu____11174 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_19  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_19) uu____11174
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11171
                                         in
                                      ([], uu____11170)
                                  | uu____11185 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11194 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11194
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11208 =
                                          let uu____11215 =
                                            let uu____11216 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____11217 =
                                              let uu____11232 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11232)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____11216 uu____11217
                                             in
                                          (uu____11215,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11208
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11157 with
                                | (tok_decls,env2) ->
                                    let uu____11257 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____11257
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____11092 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11282 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11282 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11300 =
                                               let uu____11301 =
                                                 let uu____11308 =
                                                   let uu____11309 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11309
                                                    in
                                                 (uu____11308,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11301
                                                in
                                             [uu____11300]
                                           else []  in
                                         let uu____11313 =
                                           let uu____11316 =
                                             let uu____11319 =
                                               let uu____11320 =
                                                 let uu____11327 =
                                                   let uu____11328 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11329 =
                                                     let uu____11340 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11340)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11328 uu____11329
                                                    in
                                                 (uu____11327,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11320
                                                in
                                             [uu____11319]  in
                                           FStar_List.append karr uu____11316
                                            in
                                         FStar_List.append decls1 uu____11313
                                      in
                                   let aux =
                                     let uu____11356 =
                                       let uu____11359 =
                                         inversion_axioms tapp vars  in
                                       let uu____11362 =
                                         let uu____11365 =
                                           let uu____11366 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11366 env2
                                             tapp vars
                                            in
                                         [uu____11365]  in
                                       FStar_List.append uu____11359
                                         uu____11362
                                        in
                                     FStar_List.append kindingAx uu____11356
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11373,uu____11374,uu____11375,uu____11376,uu____11377)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11385,t,uu____11387,n_tps,uu____11389) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11397 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11397 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11437 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11437 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11458 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11458 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11472 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11472 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11542 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11542,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11544 =
                                  let uu____11563 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11563, true)
                                   in
                                let uu____11572 =
                                  let uu____11595 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____11595
                                   in
                                FStar_All.pipe_right uu____11544 uu____11572
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
                              let uu____11626 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11626 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11638::uu____11639 ->
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
                                         let uu____11684 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____11685 =
                                           let uu____11696 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11696)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11684 uu____11685
                                     | uu____11721 -> tok_typing  in
                                   let uu____11730 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11730 with
                                    | (vars',guards',env'',decls_formals,uu____11755)
                                        ->
                                        let uu____11768 =
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
                                        (match uu____11768 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11799 ->
                                                   let uu____11806 =
                                                     let uu____11807 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11807
                                                      in
                                                   [uu____11806]
                                                in
                                             let encode_elim uu____11819 =
                                               let uu____11820 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11820 with
                                               | (head1,args) ->
                                                   let uu____11863 =
                                                     let uu____11864 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11864.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11863 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11874;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11875;_},uu____11876)
                                                        ->
                                                        let uu____11881 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11881
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11894
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11894
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
                                                                    uu____11943
                                                                    ->
                                                                    let uu____11944
                                                                    =
                                                                    let uu____11949
                                                                    =
                                                                    let uu____11950
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11950
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11949)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11944
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11966
                                                                    =
                                                                    let uu____11967
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11967
                                                                     in
                                                                    if
                                                                    uu____11966
                                                                    then
                                                                    let uu____11980
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11980]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11982
                                                                    =
                                                                    let uu____11995
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12045
                                                                     ->
                                                                    fun
                                                                    uu____12046
                                                                     ->
                                                                    match 
                                                                    (uu____12045,
                                                                    uu____12046)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12141
                                                                    =
                                                                    let uu____12148
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12148
                                                                     in
                                                                    (match uu____12141
                                                                    with
                                                                    | 
                                                                    (uu____12161,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12169
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12169
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12171
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12171
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
                                                                    uu____11995
                                                                     in
                                                                  (match uu____11982
                                                                   with
                                                                   | 
                                                                   (uu____12186,arg_vars,elim_eqns_or_guards,uu____12189)
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
                                                                    let uu____12217
                                                                    =
                                                                    let uu____12224
                                                                    =
                                                                    let uu____12225
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12226
                                                                    =
                                                                    let uu____12237
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12248
                                                                    =
                                                                    let uu____12249
                                                                    =
                                                                    let uu____12254
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12254)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12249
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12237,
                                                                    uu____12248)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12225
                                                                    uu____12226
                                                                     in
                                                                    (uu____12224,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12217
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12273
                                                                    =
                                                                    let uu____12278
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12278,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12273
                                                                     in
                                                                    let uu____12279
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12279
                                                                    then
                                                                    let x =
                                                                    let uu____12285
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12285,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12287
                                                                    =
                                                                    let uu____12294
                                                                    =
                                                                    let uu____12295
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12296
                                                                    =
                                                                    let uu____12307
                                                                    =
                                                                    let uu____12312
                                                                    =
                                                                    let uu____12315
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12315]
                                                                     in
                                                                    [uu____12312]
                                                                     in
                                                                    let uu____12320
                                                                    =
                                                                    let uu____12321
                                                                    =
                                                                    let uu____12326
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12327
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12326,
                                                                    uu____12327)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12321
                                                                     in
                                                                    (uu____12307,
                                                                    [x],
                                                                    uu____12320)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12295
                                                                    uu____12296
                                                                     in
                                                                    let uu____12346
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12294,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12346)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12287
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12353
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
                                                                    (let uu____12381
                                                                    =
                                                                    let uu____12382
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12382
                                                                    dapp1  in
                                                                    [uu____12381])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12353
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12389
                                                                    =
                                                                    let uu____12396
                                                                    =
                                                                    let uu____12397
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12398
                                                                    =
                                                                    let uu____12409
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12420
                                                                    =
                                                                    let uu____12421
                                                                    =
                                                                    let uu____12426
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12426)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12421
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12409,
                                                                    uu____12420)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12397
                                                                    uu____12398
                                                                     in
                                                                    (uu____12396,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12389)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12446 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12446
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12459
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12459
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
                                                                    uu____12508
                                                                    ->
                                                                    let uu____12509
                                                                    =
                                                                    let uu____12514
                                                                    =
                                                                    let uu____12515
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12515
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12514)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12509
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12531
                                                                    =
                                                                    let uu____12532
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12532
                                                                     in
                                                                    if
                                                                    uu____12531
                                                                    then
                                                                    let uu____12545
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12545]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12547
                                                                    =
                                                                    let uu____12560
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12610
                                                                     ->
                                                                    fun
                                                                    uu____12611
                                                                     ->
                                                                    match 
                                                                    (uu____12610,
                                                                    uu____12611)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12706
                                                                    =
                                                                    let uu____12713
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12713
                                                                     in
                                                                    (match uu____12706
                                                                    with
                                                                    | 
                                                                    (uu____12726,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12734
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12734
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12736
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
                                                                    uu____12560
                                                                     in
                                                                  (match uu____12547
                                                                   with
                                                                   | 
                                                                   (uu____12751,arg_vars,elim_eqns_or_guards,uu____12754)
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
                                                                    let uu____12782
                                                                    =
                                                                    let uu____12789
                                                                    =
                                                                    let uu____12790
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12791
                                                                    =
                                                                    let uu____12802
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12813
                                                                    =
                                                                    let uu____12814
                                                                    =
                                                                    let uu____12819
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12819)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12814
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12802,
                                                                    uu____12813)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12790
                                                                    uu____12791
                                                                     in
                                                                    (uu____12789,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12782
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12838
                                                                    =
                                                                    let uu____12843
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12843,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12838
                                                                     in
                                                                    let uu____12844
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12844
                                                                    then
                                                                    let x =
                                                                    let uu____12850
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12850,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12852
                                                                    =
                                                                    let uu____12859
                                                                    =
                                                                    let uu____12860
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12861
                                                                    =
                                                                    let uu____12872
                                                                    =
                                                                    let uu____12877
                                                                    =
                                                                    let uu____12880
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12880]
                                                                     in
                                                                    [uu____12877]
                                                                     in
                                                                    let uu____12885
                                                                    =
                                                                    let uu____12886
                                                                    =
                                                                    let uu____12891
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12891,
                                                                    uu____12892)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12886
                                                                     in
                                                                    (uu____12872,
                                                                    [x],
                                                                    uu____12885)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12860
                                                                    uu____12861
                                                                     in
                                                                    let uu____12911
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12859,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12911)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12852
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12918
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
                                                                    (let uu____12946
                                                                    =
                                                                    let uu____12947
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12947
                                                                    dapp1  in
                                                                    [uu____12946])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12918
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12954
                                                                    =
                                                                    let uu____12961
                                                                    =
                                                                    let uu____12962
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12963
                                                                    =
                                                                    let uu____12974
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12985
                                                                    =
                                                                    let uu____12986
                                                                    =
                                                                    let uu____12991
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12991)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12986
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12974,
                                                                    uu____12985)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12962
                                                                    uu____12963
                                                                     in
                                                                    (uu____12961,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12954)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____13010 ->
                                                        ((let uu____13012 =
                                                            let uu____13017 =
                                                              let uu____13018
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____13019
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____13018
                                                                uu____13019
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____13017)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____13012);
                                                         ([], [])))
                                                in
                                             let uu____13024 = encode_elim ()
                                                in
                                             (match uu____13024 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____13044 =
                                                      let uu____13047 =
                                                        let uu____13050 =
                                                          let uu____13053 =
                                                            let uu____13056 =
                                                              let uu____13057
                                                                =
                                                                let uu____13068
                                                                  =
                                                                  let uu____13071
                                                                    =
                                                                    let uu____13072
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____13072
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____13071
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____13068)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____13057
                                                               in
                                                            [uu____13056]  in
                                                          let uu____13077 =
                                                            let uu____13080 =
                                                              let uu____13083
                                                                =
                                                                let uu____13086
                                                                  =
                                                                  let uu____13089
                                                                    =
                                                                    let uu____13092
                                                                    =
                                                                    let uu____13095
                                                                    =
                                                                    let uu____13096
                                                                    =
                                                                    let uu____13103
                                                                    =
                                                                    let uu____13104
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13105
                                                                    =
                                                                    let uu____13116
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____13116)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13104
                                                                    uu____13105
                                                                     in
                                                                    (uu____13103,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13096
                                                                     in
                                                                    let uu____13129
                                                                    =
                                                                    let uu____13132
                                                                    =
                                                                    let uu____13133
                                                                    =
                                                                    let uu____13140
                                                                    =
                                                                    let uu____13141
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13142
                                                                    =
                                                                    let uu____13153
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____13164
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____13153,
                                                                    uu____13164)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13141
                                                                    uu____13142
                                                                     in
                                                                    (uu____13140,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13133
                                                                     in
                                                                    [uu____13132]
                                                                     in
                                                                    uu____13095
                                                                    ::
                                                                    uu____13129
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____13092
                                                                     in
                                                                  FStar_List.append
                                                                    uu____13089
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____13086
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____13083
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____13080
                                                             in
                                                          FStar_List.append
                                                            uu____13053
                                                            uu____13077
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____13050
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____13047
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____13044
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
           (fun uu____13210  ->
              fun se  ->
                match uu____13210 with
                | (g,env1) ->
                    let uu____13230 = encode_sigelt env1 se  in
                    (match uu____13230 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____13295 =
        match uu____13295 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____13327 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_TypeChecker_Env.Binding_var x ->
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
                 ((let uu____13333 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13333
                   then
                     let uu____13334 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13335 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13336 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13334 uu____13335 uu____13336
                   else ());
                  (let uu____13338 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13338 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13354 =
                         let uu____13361 =
                           let uu____13362 =
                             let uu____13363 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13363
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13362  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13361
                          in
                       (match uu____13354 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13379 = FStar_Options.log_queries ()
                                 in
                              if uu____13379
                              then
                                let uu____13382 =
                                  let uu____13383 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13384 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13385 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13383 uu____13384 uu____13385
                                   in
                                FStar_Pervasives_Native.Some uu____13382
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____13401,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13415 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13415 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____13438,se,uu____13440) ->
                 let uu____13445 = encode_sigelt env1 se  in
                 (match uu____13445 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____13462,se) ->
                 let uu____13468 = encode_sigelt env1 se  in
                 (match uu____13468 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13485 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13485 with | (uu____13508,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13523 'Auu____13524 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13523,'Auu____13524)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13593  ->
              match uu____13593 with
              | (l,uu____13605,uu____13606) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13652  ->
              match uu____13652 with
              | (l,uu____13666,uu____13667) ->
                  let uu____13676 =
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_SMTEncoding_Term.Echo _0_20)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13677 =
                    let uu____13680 =
                      let uu____13681 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13681  in
                    [uu____13680]  in
                  uu____13676 :: uu____13677))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13708 =
      let uu____13711 =
        let uu____13712 = FStar_Util.psmap_empty ()  in
        let uu____13727 = FStar_Util.psmap_empty ()  in
        let uu____13730 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13733 =
          let uu____13734 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13734 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13712;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13727;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13730;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13733;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13711]  in
    FStar_ST.op_Colon_Equals last_env uu____13708
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13772 = FStar_ST.op_Bang last_env  in
      match uu____13772 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13803 ->
          let uu___117_13806 = e  in
          let uu____13807 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___117_13806.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___117_13806.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___117_13806.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___117_13806.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___117_13806.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___117_13806.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___117_13806.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___117_13806.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13807;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___117_13806.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13813 = FStar_ST.op_Bang last_env  in
    match uu____13813 with
    | [] -> failwith "Empty env stack"
    | uu____13843::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13878  ->
    let uu____13879 = FStar_ST.op_Bang last_env  in
    match uu____13879 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top =
          let uu___118_13914 = hd1  in
          let uu____13915 =
            FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___118_13914.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___118_13914.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___118_13914.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___118_13914.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___118_13914.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = uu____13915;
            FStar_SMTEncoding_Env.nolabels =
              (uu___118_13914.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___118_13914.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___118_13914.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___118_13914.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___118_13914.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13949  ->
    let uu____13950 = FStar_ST.op_Bang last_env  in
    match uu____13950 with
    | [] -> failwith "Popping an empty stack"
    | uu____13980::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____14019  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____14062  ->
         let uu____14063 = snapshot_env ()  in
         match uu____14063 with
         | (env_depth,()) ->
             let uu____14079 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____14079 with
              | (varops_depth,()) ->
                  let uu____14095 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____14095 with
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
        (fun uu____14138  ->
           let uu____14139 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____14139 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____14207 = snapshot msg  in () 
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
        | (uu____14248::uu____14249,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___119_14257 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___119_14257.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___119_14257.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___119_14257.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____14258 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____14277 =
        let uu____14280 =
          let uu____14281 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____14281  in
        let uu____14282 = open_fact_db_tags env  in uu____14280 ::
          uu____14282
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____14277
  
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
      let uu____14308 = encode_sigelt env se  in
      match uu____14308 with
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
        let uu____14350 = FStar_Options.log_queries ()  in
        if uu____14350
        then
          let uu____14353 =
            let uu____14354 =
              let uu____14355 =
                let uu____14356 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14356 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14355  in
            FStar_SMTEncoding_Term.Caption uu____14354  in
          uu____14353 :: decls
        else decls  in
      (let uu____14367 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14367
       then
         let uu____14368 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14368
       else ());
      (let env =
         let uu____14371 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14371 tcenv  in
       let uu____14372 = encode_top_level_facts env se  in
       match uu____14372 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14386 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14386)))
  
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
      (let uu____14402 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14402
       then
         let uu____14403 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14403
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14442  ->
                 fun se  ->
                   match uu____14442 with
                   | (g,env2) ->
                       let uu____14462 = encode_top_level_facts env2 se  in
                       (match uu____14462 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14485 =
         encode_signature
           (let uu___120_14494 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___120_14494.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___120_14494.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___120_14494.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___120_14494.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___120_14494.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___120_14494.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___120_14494.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___120_14494.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___120_14494.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___120_14494.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14485 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14513 = FStar_Options.log_queries ()  in
             if uu____14513
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___121_14521 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___121_14521.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___121_14521.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___121_14521.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___121_14521.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___121_14521.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___121_14521.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___121_14521.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___121_14521.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___121_14521.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___121_14521.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14523 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14523
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
        (let uu____14581 =
           let uu____14582 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14582.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14581);
        (let env =
           let uu____14584 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14584 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____14596 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____14633 = aux rest  in
                 (match uu____14633 with
                  | (out,rest1) ->
                      let t =
                        let uu____14663 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14663 with
                        | FStar_Pervasives_Native.Some uu____14668 ->
                            let uu____14669 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14669
                              x.FStar_Syntax_Syntax.sort
                        | uu____14670 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14674 =
                        let uu____14677 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___122_14680 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___122_14680.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___122_14680.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14677 :: out  in
                      (uu____14674, rest1))
             | uu____14685 -> ([], bindings1)  in
           let uu____14692 = aux bindings  in
           match uu____14692 with
           | (closing,bindings1) ->
               let uu____14717 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14717, bindings1)
            in
         match uu____14596 with
         | (q1,bindings1) ->
             let uu____14740 =
               let uu____14745 =
                 FStar_List.filter
                   (fun uu___104_14750  ->
                      match uu___104_14750 with
                      | FStar_TypeChecker_Env.Binding_sig uu____14751 ->
                          false
                      | uu____14758 -> true) bindings1
                  in
               encode_env_bindings env uu____14745  in
             (match uu____14740 with
              | (env_decls,env1) ->
                  ((let uu____14776 =
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
                    if uu____14776
                    then
                      let uu____14777 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14777
                    else ());
                   (let uu____14779 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14779 with
                    | (phi,qdecls) ->
                        let uu____14800 =
                          let uu____14805 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14805 phi
                           in
                        (match uu____14800 with
                         | (labels,phi1) ->
                             let uu____14822 = encode_labels labels  in
                             (match uu____14822 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14859 =
                                      let uu____14866 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14867 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14866,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14867)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14859
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
  