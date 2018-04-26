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
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
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
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____2677 =
        let uu____2678 =
          let uu____2685 =
            let uu____2688 =
              let uu____2691 =
                let uu____2694 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____2695 =
                  let uu____2698 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____2698]  in
                uu____2694 :: uu____2695  in
              tt :: uu____2691  in
            tt :: uu____2688  in
          ("Prims.Precedes", uu____2685)  in
        FStar_SMTEncoding_Util.mkApp uu____2678  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2677  in
    let precedes_y_x =
      let uu____2702 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2702  in
    let uu____2705 =
      let uu____2706 =
        let uu____2713 =
          let uu____2714 = FStar_TypeChecker_Env.get_range env  in
          let uu____2715 =
            let uu____2726 =
              let uu____2731 =
                let uu____2734 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2734]  in
              [uu____2731]  in
            let uu____2739 =
              let uu____2740 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2740 tt  in
            (uu____2726, [bb], uu____2739)  in
          FStar_SMTEncoding_Term.mkForall uu____2714 uu____2715  in
        (uu____2713, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2706  in
    let uu____2761 =
      let uu____2764 =
        let uu____2765 =
          let uu____2772 =
            let uu____2773 =
              let uu____2784 =
                let uu____2785 =
                  let uu____2790 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2790)  in
                FStar_SMTEncoding_Util.mkImp uu____2785  in
              ([[typing_pred]], [xx], uu____2784)  in
            let uu____2813 =
              let uu____2828 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2828  in
            uu____2813 uu____2773  in
          (uu____2772, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2765  in
      let uu____2831 =
        let uu____2834 =
          let uu____2835 =
            let uu____2842 =
              let uu____2843 =
                let uu____2854 =
                  let uu____2855 =
                    let uu____2860 =
                      let uu____2861 =
                        let uu____2864 =
                          let uu____2867 =
                            let uu____2870 =
                              let uu____2871 =
                                let uu____2876 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2877 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2876, uu____2877)  in
                              FStar_SMTEncoding_Util.mkGT uu____2871  in
                            let uu____2878 =
                              let uu____2881 =
                                let uu____2882 =
                                  let uu____2887 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2888 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2887, uu____2888)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2882  in
                              let uu____2889 =
                                let uu____2892 =
                                  let uu____2893 =
                                    let uu____2898 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2899 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2898, uu____2899)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2893  in
                                [uu____2892]  in
                              uu____2881 :: uu____2889  in
                            uu____2870 :: uu____2878  in
                          typing_pred_y :: uu____2867  in
                        typing_pred :: uu____2864  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2861  in
                    (uu____2860, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2855  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2854)
                 in
              let uu____2926 =
                let uu____2941 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2941  in
              uu____2926 uu____2843  in
            (uu____2842,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2835  in
        [uu____2834]  in
      uu____2764 :: uu____2831  in
    uu____2705 :: uu____2761  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2967 =
      let uu____2968 =
        let uu____2975 =
          let uu____2976 = FStar_TypeChecker_Env.get_range env  in
          let uu____2977 =
            let uu____2988 =
              let uu____2993 =
                let uu____2996 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2996]  in
              [uu____2993]  in
            let uu____3001 =
              let uu____3002 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3002 tt  in
            (uu____2988, [bb], uu____3001)  in
          FStar_SMTEncoding_Term.mkForall uu____2976 uu____2977  in
        (uu____2975, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2968  in
    let uu____3023 =
      let uu____3026 =
        let uu____3027 =
          let uu____3034 =
            let uu____3035 =
              let uu____3046 =
                let uu____3047 =
                  let uu____3052 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3052)  in
                FStar_SMTEncoding_Util.mkImp uu____3047  in
              ([[typing_pred]], [xx], uu____3046)  in
            let uu____3075 =
              let uu____3090 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3090  in
            uu____3075 uu____3035  in
          (uu____3034, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3027  in
      [uu____3026]  in
    uu____2967 :: uu____3023  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3133 =
      let uu____3134 =
        let uu____3141 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3141, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3134  in
    [uu____3133]  in
  let mk_and_interp env conj uu____3159 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3184 =
      let uu____3185 =
        let uu____3192 =
          let uu____3193 = FStar_TypeChecker_Env.get_range env  in
          let uu____3194 =
            let uu____3205 =
              let uu____3206 =
                let uu____3211 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3211, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3206  in
            ([[l_and_a_b]], [aa; bb], uu____3205)  in
          FStar_SMTEncoding_Term.mkForall uu____3193 uu____3194  in
        (uu____3192, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3185  in
    [uu____3184]  in
  let mk_or_interp env disj uu____3255 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3280 =
      let uu____3281 =
        let uu____3288 =
          let uu____3289 = FStar_TypeChecker_Env.get_range env  in
          let uu____3290 =
            let uu____3301 =
              let uu____3302 =
                let uu____3307 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3307, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3302  in
            ([[l_or_a_b]], [aa; bb], uu____3301)  in
          FStar_SMTEncoding_Term.mkForall uu____3289 uu____3290  in
        (uu____3288, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3281  in
    [uu____3280]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3376 =
      let uu____3377 =
        let uu____3384 =
          let uu____3385 = FStar_TypeChecker_Env.get_range env  in
          let uu____3386 =
            let uu____3397 =
              let uu____3398 =
                let uu____3403 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3403, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3398  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3397)  in
          FStar_SMTEncoding_Term.mkForall uu____3385 uu____3386  in
        (uu____3384, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3377  in
    [uu____3376]  in
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
    let uu____3482 =
      let uu____3483 =
        let uu____3490 =
          let uu____3491 = FStar_TypeChecker_Env.get_range env  in
          let uu____3492 =
            let uu____3503 =
              let uu____3504 =
                let uu____3509 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3509, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3504  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3503)  in
          FStar_SMTEncoding_Term.mkForall uu____3491 uu____3492  in
        (uu____3490, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3483  in
    [uu____3482]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3586 =
      let uu____3587 =
        let uu____3594 =
          let uu____3595 = FStar_TypeChecker_Env.get_range env  in
          let uu____3596 =
            let uu____3607 =
              let uu____3608 =
                let uu____3613 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3613, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3608  in
            ([[l_imp_a_b]], [aa; bb], uu____3607)  in
          FStar_SMTEncoding_Term.mkForall uu____3595 uu____3596  in
        (uu____3594, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3587  in
    [uu____3586]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3682 =
      let uu____3683 =
        let uu____3690 =
          let uu____3691 = FStar_TypeChecker_Env.get_range env  in
          let uu____3692 =
            let uu____3703 =
              let uu____3704 =
                let uu____3709 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3709, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3704  in
            ([[l_iff_a_b]], [aa; bb], uu____3703)  in
          FStar_SMTEncoding_Term.mkForall uu____3691 uu____3692  in
        (uu____3690, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3683  in
    [uu____3682]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3767 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3767  in
    let uu____3770 =
      let uu____3771 =
        let uu____3778 =
          let uu____3779 = FStar_TypeChecker_Env.get_range env  in
          let uu____3780 =
            let uu____3791 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3791)  in
          FStar_SMTEncoding_Term.mkForall uu____3779 uu____3780  in
        (uu____3778, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3771  in
    [uu____3770]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3835 =
      let uu____3836 =
        let uu____3843 =
          let uu____3844 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3844 range_ty  in
        let uu____3845 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3843, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3845)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3836  in
    [uu____3835]  in
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
        let uu____3885 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3885 x1 t  in
      let uu____3886 = FStar_TypeChecker_Env.get_range env  in
      let uu____3887 =
        let uu____3898 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3898)  in
      FStar_SMTEncoding_Term.mkForall uu____3886 uu____3887  in
    let uu____3921 =
      let uu____3922 =
        let uu____3929 =
          let uu____3930 = FStar_TypeChecker_Env.get_range env  in
          let uu____3931 =
            let uu____3942 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3942)  in
          FStar_SMTEncoding_Term.mkForall uu____3930 uu____3931  in
        (uu____3929,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3922  in
    [uu____3921]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3998 =
      let uu____3999 =
        let uu____4006 =
          let uu____4007 = FStar_TypeChecker_Env.get_range env  in
          let uu____4008 =
            let uu____4023 =
              let uu____4024 =
                let uu____4029 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4030 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4029, uu____4030)  in
              FStar_SMTEncoding_Util.mkAnd uu____4024  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4023)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4007 uu____4008  in
        (uu____4006,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3999  in
    [uu____3998]  in
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
          let uu____4446 =
            FStar_Util.find_opt
              (fun uu____4478  ->
                 match uu____4478 with
                 | (l,uu____4490) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4446 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4524,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4575 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4575 with
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
              let uu____4627 =
                ((let uu____4630 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4630) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4627
              then
                let arg_sorts =
                  let uu____4640 =
                    let uu____4641 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4641.FStar_Syntax_Syntax.n  in
                  match uu____4640 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4647) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4677  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4682 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4684 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4684 with
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
                (let uu____4717 = prims.is lid  in
                 if uu____4717
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4725 = prims.mk lid vname  in
                   match uu____4725 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4752 =
                      let uu____4763 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4763 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4781 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4781
                            then
                              let uu____4782 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___82_4785 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___82_4785.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___82_4785.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___82_4785.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___82_4785.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___82_4785.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___82_4785.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___82_4785.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___82_4785.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___82_4785.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___82_4785.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___82_4785.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___82_4785.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___82_4785.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___82_4785.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___82_4785.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___82_4785.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___82_4785.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___82_4785.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___82_4785.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___82_4785.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___82_4785.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___82_4785.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___82_4785.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___82_4785.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___82_4785.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___82_4785.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___82_4785.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___82_4785.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___82_4785.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___82_4785.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___82_4785.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___82_4785.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___82_4785.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___82_4785.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___82_4785.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___82_4785.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4782
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4797 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4797)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4752 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4847 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4847 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4872 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___71_4922  ->
                                       match uu___71_4922 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4926 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4926 with
                                            | (uu____4947,(xxsym,uu____4949))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4967 =
                                                  let uu____4968 =
                                                    let uu____4975 =
                                                      let uu____4976 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4977 =
                                                        let uu____4988 =
                                                          let uu____4989 =
                                                            let uu____4994 =
                                                              let uu____4995
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4995
                                                               in
                                                            (vapp,
                                                              uu____4994)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4989
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4988)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4976 uu____4977
                                                       in
                                                    (uu____4975,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4968
                                                   in
                                                [uu____4967])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____5014 =
                                             FStar_Util.prefix vars  in
                                           (match uu____5014 with
                                            | (uu____5035,(xxsym,uu____5037))
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
                                                let uu____5060 =
                                                  let uu____5061 =
                                                    let uu____5068 =
                                                      let uu____5069 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5070 =
                                                        let uu____5081 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5081)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5069 uu____5070
                                                       in
                                                    (uu____5068,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5061
                                                   in
                                                [uu____5060])
                                       | uu____5098 -> []))
                                in
                             let uu____5099 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5099 with
                              | (vars,guards,env',decls1,uu____5126) ->
                                  let uu____5139 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5148 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5148, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5150 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5150 with
                                         | (g,ds) ->
                                             let uu____5161 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5161,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5139 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5174 =
                                           let uu____5181 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5181)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5174
                                          in
                                       let uu____5190 =
                                         let vname_decl =
                                           let uu____5198 =
                                             let uu____5209 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5219  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5209,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5198
                                            in
                                         let uu____5228 =
                                           let env2 =
                                             let uu___83_5234 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___83_5234.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____5235 =
                                             let uu____5236 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5236  in
                                           if uu____5235
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5228 with
                                         | (tok_typing,decls2) ->
                                             let uu____5250 =
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
                                                   let uu____5270 =
                                                     let uu____5271 =
                                                       let uu____5274 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____5274
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____5271
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____5270)
                                               | uu____5283 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____5290 =
                                                       let uu____5297 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____5297]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____5290
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____5304 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____5305 =
                                                       let uu____5316 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____5316)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____5304 uu____5305
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5328 =
                                                       let uu____5335 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____5335,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5328
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
                                                       let uu____5364 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5365 =
                                                         let uu____5376 =
                                                           let uu____5377 =
                                                             let uu____5382 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____5383 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____5382,
                                                               uu____5383)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____5377
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____5376)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5364
                                                         uu____5365
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
                                             (match uu____5250 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5190 with
                                        | (decls2,env2) ->
                                            let uu____5436 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5444 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5444 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5457 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5457,
                                                    decls)
                                               in
                                            (match uu____5436 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5468 =
                                                     let uu____5475 =
                                                       let uu____5476 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5477 =
                                                         let uu____5488 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5488)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5476
                                                         uu____5477
                                                        in
                                                     (uu____5475,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5468
                                                    in
                                                 let freshness =
                                                   let uu____5504 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5504
                                                   then
                                                     let uu____5509 =
                                                       let uu____5510 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5511 =
                                                         let uu____5522 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5533 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5522,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5533)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5510
                                                         uu____5511
                                                        in
                                                     let uu____5536 =
                                                       let uu____5539 =
                                                         let uu____5540 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5540 env2
                                                           vapp vars
                                                          in
                                                       [uu____5539]  in
                                                     uu____5509 :: uu____5536
                                                   else []  in
                                                 let g =
                                                   let uu____5545 =
                                                     let uu____5548 =
                                                       let uu____5551 =
                                                         let uu____5554 =
                                                           let uu____5557 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5557
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5554
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5551
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5548
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5545
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
          let uu____5590 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5590 with
          | FStar_Pervasives_Native.None  ->
              let uu____5601 = encode_free_var false env x t t_norm []  in
              (match uu____5601 with
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
            let uu____5664 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5664 with
            | (decls,env1) ->
                let uu____5683 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5683
                then
                  let uu____5690 =
                    let uu____5693 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5693  in
                  (uu____5690, env1)
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
             (fun uu____5751  ->
                fun lb  ->
                  match uu____5751 with
                  | (decls,env1) ->
                      let uu____5771 =
                        let uu____5778 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5778
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5771 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5801 = FStar_Syntax_Util.head_and_args t  in
    match uu____5801 with
    | (hd1,args) ->
        let uu____5838 =
          let uu____5839 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5839.FStar_Syntax_Syntax.n  in
        (match uu____5838 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5843,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5862 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5868 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5896  ->
      fun quals  ->
        match uu____5896 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5980 = FStar_Util.first_N nbinders formals  in
              match uu____5980 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6061  ->
                         fun uu____6062  ->
                           match (uu____6061, uu____6062) with
                           | ((formal,uu____6080),(binder,uu____6082)) ->
                               let uu____6091 =
                                 let uu____6098 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6098)  in
                               FStar_Syntax_Syntax.NT uu____6091) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6106 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6137  ->
                              match uu____6137 with
                              | (x,i) ->
                                  let uu____6148 =
                                    let uu___84_6149 = x  in
                                    let uu____6150 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___84_6149.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___84_6149.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6150
                                    }  in
                                  (uu____6148, i)))
                       in
                    FStar_All.pipe_right uu____6106
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6168 =
                      let uu____6173 = FStar_Syntax_Subst.compress body  in
                      let uu____6174 =
                        let uu____6175 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6175
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6173 uu____6174
                       in
                    uu____6168 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6244 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6244
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___85_6247 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___85_6247.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___85_6247.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___85_6247.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___85_6247.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___85_6247.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___85_6247.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___85_6247.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___85_6247.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___85_6247.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___85_6247.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___85_6247.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___85_6247.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___85_6247.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___85_6247.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___85_6247.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___85_6247.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___85_6247.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___85_6247.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___85_6247.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___85_6247.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___85_6247.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___85_6247.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___85_6247.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___85_6247.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___85_6247.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___85_6247.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___85_6247.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___85_6247.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___85_6247.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___85_6247.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___85_6247.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___85_6247.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___85_6247.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___85_6247.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___85_6247.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___85_6247.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6284 = FStar_Syntax_Util.abs_formals e  in
                match uu____6284 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6348::uu____6349 ->
                         let uu____6364 =
                           let uu____6365 =
                             let uu____6368 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6368
                              in
                           uu____6365.FStar_Syntax_Syntax.n  in
                         (match uu____6364 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6411 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6411 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6453 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6453
                                   then
                                     let uu____6488 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6488 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6582  ->
                                                   fun uu____6583  ->
                                                     match (uu____6582,
                                                             uu____6583)
                                                     with
                                                     | ((x,uu____6601),
                                                        (b,uu____6603)) ->
                                                         let uu____6612 =
                                                           let uu____6619 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6619)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6612)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6621 =
                                            let uu____6642 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6642)  in
                                          (uu____6621, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6710 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6710 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6799) ->
                              let uu____6804 =
                                let uu____6825 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6825  in
                              (uu____6804, true)
                          | uu____6890 when Prims.op_Negation norm1 ->
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
                          | uu____6892 ->
                              let uu____6893 =
                                let uu____6894 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6895 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6894 uu____6895
                                 in
                              failwith uu____6893)
                     | uu____6920 ->
                         let rec aux' t_norm2 =
                           let uu____6947 =
                             let uu____6948 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6948.FStar_Syntax_Syntax.n  in
                           match uu____6947 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6989 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6989 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____7017 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____7017 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7097) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7102 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____7158 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____7158
               then encode_top_level_vals env bindings quals
               else
                 (let uu____7170 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____7233  ->
                            fun lb  ->
                              match uu____7233 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____7288 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____7288
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____7291 =
                                      let uu____7300 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____7300
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____7291 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____7170 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7425 =
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
                        | uu____7431 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7439 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7439 vars)
                            else
                              (let uu____7441 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7441)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7501;
                             FStar_Syntax_Syntax.lbeff = uu____7502;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7504;
                             FStar_Syntax_Syntax.lbpos = uu____7505;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7529 =
                              let uu____7536 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7536 with
                              | (tcenv',uu____7554,e_t) ->
                                  let uu____7560 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7571 -> failwith "Impossible"  in
                                  (match uu____7560 with
                                   | (e1,t_norm1) ->
                                       ((let uu___88_7587 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___88_7587.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___88_7587.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___88_7587.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___88_7587.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___88_7587.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____7529 with
                             | (env',e1,t_norm1) ->
                                 let uu____7597 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7597 with
                                  | ((binders,body,uu____7618,t_body),curry)
                                      ->
                                      ((let uu____7630 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7630
                                        then
                                          let uu____7631 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7632 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7631 uu____7632
                                        else ());
                                       (let uu____7634 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7634 with
                                        | (vars,guards,env'1,binder_decls,uu____7661)
                                            ->
                                            let body1 =
                                              let uu____7675 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7675
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
                                              let uu____7692 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7692 curry fvb
                                                vars
                                               in
                                            let uu____7693 =
                                              let uu____7702 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7702
                                              then
                                                let uu____7713 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7714 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7713, uu____7714)
                                              else
                                                (let uu____7724 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7724))
                                               in
                                            (match uu____7693 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7747 =
                                                     let uu____7754 =
                                                       let uu____7755 =
                                                         FStar_Syntax_Util.range_of_lbname
                                                           lbn
                                                          in
                                                       let uu____7756 =
                                                         let uu____7767 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7767)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7755
                                                         uu____7756
                                                        in
                                                     let uu____7778 =
                                                       let uu____7781 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7781
                                                        in
                                                     (uu____7754, uu____7778,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7747
                                                    in
                                                 let uu____7784 =
                                                   let uu____7787 =
                                                     let uu____7790 =
                                                       let uu____7793 =
                                                         let uu____7796 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7796
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7793
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7790
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7787
                                                    in
                                                 (uu____7784, env2))))))
                        | uu____7801 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7864 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7864, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7867 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7914  ->
                                  fun fvb  ->
                                    match uu____7914 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7960 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7960
                                           in
                                        let gtok =
                                          let uu____7962 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7962
                                           in
                                        let env4 =
                                          let uu____7964 =
                                            let uu____7967 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____7967
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7964
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7867 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____8075 t_norm
                              uu____8077 =
                              match (uu____8075, uu____8077) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____8107;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____8108;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____8110;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____8111;_})
                                  ->
                                  let uu____8132 =
                                    let uu____8139 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____8139 with
                                    | (tcenv',uu____8161,e_t) ->
                                        let uu____8167 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____8178 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____8167 with
                                         | (e1,t_norm1) ->
                                             ((let uu___89_8194 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___89_8194.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____8132 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____8209 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____8209
                                         then
                                           let uu____8210 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____8211 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____8212 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____8210 uu____8211 uu____8212
                                         else ());
                                        (let uu____8214 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____8214 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____8251 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8251
                                               then
                                                 let uu____8252 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8253 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8254 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____8255 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____8252 uu____8253
                                                   uu____8254 uu____8255
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____8259 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8259 with
                                               | (vars,guards,env'1,binder_decls,uu____8290)
                                                   ->
                                                   let decl_g =
                                                     let uu____8304 =
                                                       let uu____8315 =
                                                         let uu____8318 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____8318
                                                          in
                                                       (g, uu____8315,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____8304
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
                                                     let uu____8343 =
                                                       let uu____8350 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____8350)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8343
                                                      in
                                                   let gsapp =
                                                     let uu____8360 =
                                                       let uu____8367 =
                                                         let uu____8370 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____8370 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8367)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8360
                                                      in
                                                   let gmax =
                                                     let uu____8376 =
                                                       let uu____8383 =
                                                         let uu____8386 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____8386 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8383)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8376
                                                      in
                                                   let body1 =
                                                     let uu____8392 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8392
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____8394 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____8394 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8412 =
                                                            let uu____8419 =
                                                              let uu____8420
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8421
                                                                =
                                                                let uu____8436
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
                                                                  uu____8436)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall'
                                                                uu____8420
                                                                uu____8421
                                                               in
                                                            let uu____8457 =
                                                              let uu____8460
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8460
                                                               in
                                                            (uu____8419,
                                                              uu____8457,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8412
                                                           in
                                                        let eqn_f =
                                                          let uu____8464 =
                                                            let uu____8471 =
                                                              let uu____8472
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8473
                                                                =
                                                                let uu____8484
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8484)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8472
                                                                uu____8473
                                                               in
                                                            (uu____8471,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8464
                                                           in
                                                        let eqn_g' =
                                                          let uu____8498 =
                                                            let uu____8505 =
                                                              let uu____8506
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8507
                                                                =
                                                                let uu____8518
                                                                  =
                                                                  let uu____8519
                                                                    =
                                                                    let uu____8524
                                                                    =
                                                                    let uu____8525
                                                                    =
                                                                    let uu____8532
                                                                    =
                                                                    let uu____8535
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8535
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8532)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8525
                                                                     in
                                                                    (gsapp,
                                                                    uu____8524)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8519
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8518)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8506
                                                                uu____8507
                                                               in
                                                            (uu____8505,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8498
                                                           in
                                                        let uu____8558 =
                                                          let uu____8567 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8567
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8596)
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
                                                                  let uu____8621
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8621
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8626
                                                                  =
                                                                  let uu____8633
                                                                    =
                                                                    let uu____8634
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8635
                                                                    =
                                                                    let uu____8646
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8646)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8634
                                                                    uu____8635
                                                                     in
                                                                  (uu____8633,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8626
                                                                 in
                                                              let uu____8667
                                                                =
                                                                let uu____8674
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8674
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8687
                                                                    =
                                                                    let uu____8690
                                                                    =
                                                                    let uu____8691
                                                                    =
                                                                    let uu____8698
                                                                    =
                                                                    let uu____8699
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8700
                                                                    =
                                                                    let uu____8711
                                                                    =
                                                                    let uu____8712
                                                                    =
                                                                    let uu____8717
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8717,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8712
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8711)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8699
                                                                    uu____8700
                                                                     in
                                                                    (uu____8698,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8691
                                                                     in
                                                                    [uu____8690]
                                                                     in
                                                                    (d3,
                                                                    uu____8687)
                                                                 in
                                                              (match uu____8667
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
                                                        (match uu____8558
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
                            let uu____8782 =
                              let uu____8795 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8856  ->
                                   fun uu____8857  ->
                                     match (uu____8856, uu____8857) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8982 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8982 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8795
                               in
                            (match uu____8782 with
                             | (decls2,eqns,env01) ->
                                 let uu____9055 =
                                   let isDeclFun uu___72_9069 =
                                     match uu___72_9069 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____9070 -> true
                                     | uu____9081 -> false  in
                                   let uu____9082 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____9082
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____9055 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____9122 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___73_9126  ->
                                 match uu___73_9126 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9127 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____9133 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____9133)))
                         in
                      if uu____9122
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
                   let uu____9185 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9185
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
        let uu____9246 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9246 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9250 = encode_sigelt' env se  in
      match uu____9250 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9266 =
                  let uu____9267 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9267  in
                [uu____9266]
            | uu____9268 ->
                let uu____9269 =
                  let uu____9272 =
                    let uu____9273 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9273  in
                  uu____9272 :: g  in
                let uu____9274 =
                  let uu____9277 =
                    let uu____9278 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9278  in
                  [uu____9277]  in
                FStar_List.append uu____9269 uu____9274
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
        let uu____9293 =
          let uu____9294 = FStar_Syntax_Subst.compress t  in
          uu____9294.FStar_Syntax_Syntax.n  in
        match uu____9293 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9298)) -> s = "opaque_to_smt"
        | uu____9299 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9306 =
          let uu____9307 = FStar_Syntax_Subst.compress t  in
          uu____9307.FStar_Syntax_Syntax.n  in
        match uu____9306 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9311)) -> s = "uninterpreted_by_smt"
        | uu____9312 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9317 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9322 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9333 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9336 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9339 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9354 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9358 =
            let uu____9359 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____9359 Prims.op_Negation  in
          if uu____9358
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9387 ->
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
               let uu____9411 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9411 with
               | (formals,uu____9429) ->
                   let arity = FStar_List.length formals  in
                   let uu____9447 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9447 with
                    | (aname,atok,env2) ->
                        let uu____9467 =
                          let uu____9472 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9472
                            env2
                           in
                        (match uu____9467 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9484 =
                                 let uu____9485 =
                                   let uu____9496 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9512  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9496,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9485
                                  in
                               [uu____9484;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9525 =
                               let aux uu____9581 uu____9582 =
                                 match (uu____9581, uu____9582) with
                                 | ((bv,uu____9634),(env3,acc_sorts,acc)) ->
                                     let uu____9672 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9672 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9525 with
                              | (uu____9744,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9767 =
                                      let uu____9774 =
                                        let uu____9775 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9776 =
                                          let uu____9787 =
                                            let uu____9788 =
                                              let uu____9793 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9793)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9788
                                             in
                                          ([[app]], xs_sorts, uu____9787)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9775 uu____9776
                                         in
                                      (uu____9774,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9767
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
                                    let uu____9813 =
                                      let uu____9820 =
                                        let uu____9821 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9822 =
                                          let uu____9833 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9833)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9821 uu____9822
                                         in
                                      (uu____9820,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9813
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9852 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9852 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9880,uu____9881) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9882 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9882 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9899,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9905 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___74_9909  ->
                      match uu___74_9909 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9910 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9915 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9916 -> false))
               in
            Prims.op_Negation uu____9905  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9925 =
               let uu____9932 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9932 env fv t quals  in
             match uu____9925 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9947 =
                   let uu____9950 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9950  in
                 (uu____9947, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9958 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9958 with
           | (uu____9967,f1) ->
               let uu____9969 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env  in
               (match uu____9969 with
                | (f2,decls) ->
                    let g =
                      let uu____9983 =
                        let uu____9984 =
                          let uu____9991 =
                            let uu____9994 =
                              let uu____9995 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9995
                               in
                            FStar_Pervasives_Native.Some uu____9994  in
                          let uu____9996 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____9991, uu____9996)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9984  in
                      [uu____9983]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10002) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____10014 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____10032 =
                       let uu____10035 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____10035.FStar_Syntax_Syntax.fv_name  in
                     uu____10032.FStar_Syntax_Syntax.v  in
                   let uu____10036 =
                     let uu____10037 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____10037  in
                   if uu____10036
                   then
                     let val_decl =
                       let uu___92_10065 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___92_10065.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___92_10065.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___92_10065.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10070 = encode_sigelt' env1 val_decl  in
                     match uu____10070 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____10014 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10098,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10100;
                          FStar_Syntax_Syntax.lbtyp = uu____10101;
                          FStar_Syntax_Syntax.lbeff = uu____10102;
                          FStar_Syntax_Syntax.lbdef = uu____10103;
                          FStar_Syntax_Syntax.lbattrs = uu____10104;
                          FStar_Syntax_Syntax.lbpos = uu____10105;_}::[]),uu____10106)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10129 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10129 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10158 =
                   let uu____10161 =
                     let uu____10162 =
                       let uu____10169 =
                         let uu____10170 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10171 =
                           let uu____10182 =
                             let uu____10183 =
                               let uu____10188 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10188)  in
                             FStar_SMTEncoding_Util.mkEq uu____10183  in
                           ([[b2t_x]], [xx], uu____10182)  in
                         FStar_SMTEncoding_Term.mkForall uu____10170
                           uu____10171
                          in
                       (uu____10169,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10162  in
                   [uu____10161]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10158
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10221,uu____10222) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___75_10231  ->
                  match uu___75_10231 with
                  | FStar_Syntax_Syntax.Discriminator uu____10232 -> true
                  | uu____10233 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10236,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10247 =
                     let uu____10248 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10248.FStar_Ident.idText  in
                   uu____10247 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___76_10252  ->
                     match uu___76_10252 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10253 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10257) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___77_10274  ->
                  match uu___77_10274 with
                  | FStar_Syntax_Syntax.Projector uu____10275 -> true
                  | uu____10280 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10283 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10283 with
           | FStar_Pervasives_Native.Some uu____10290 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___93_10294 = se  in
                 let uu____10295 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10295;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___93_10294.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___93_10294.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___93_10294.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10302) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10320) ->
          let uu____10329 = encode_sigelts env ses  in
          (match uu____10329 with
           | (g,env1) ->
               let uu____10346 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___78_10369  ->
                         match uu___78_10369 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10370;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10371;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10372;_}
                             -> false
                         | uu____10375 -> true))
                  in
               (match uu____10346 with
                | (g',inversions) ->
                    let uu____10390 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___79_10411  ->
                              match uu___79_10411 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10412 ->
                                  true
                              | uu____10423 -> false))
                       in
                    (match uu____10390 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10441,tps,k,uu____10444,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___80_10461  ->
                    match uu___80_10461 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10462 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10473 = c  in
              match uu____10473 with
              | (name,args,uu____10478,uu____10479,uu____10480) ->
                  let uu____10485 =
                    let uu____10486 =
                      let uu____10497 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10514  ->
                                match uu____10514 with
                                | (uu____10521,sort,uu____10523) -> sort))
                         in
                      (name, uu____10497, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10486  in
                  [uu____10485]
            else
              (let uu____10529 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____10529 c)
             in
          let inversion_axioms tapp vars =
            let uu____10555 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10561 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10561 FStar_Option.isNone))
               in
            if uu____10555
            then []
            else
              (let uu____10593 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10593 with
               | (xxsym,xx) ->
                   let uu____10602 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10641  ->
                             fun l  ->
                               match uu____10641 with
                               | (out,decls) ->
                                   let uu____10661 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10661 with
                                    | (uu____10672,data_t) ->
                                        let uu____10674 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10674 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10720 =
                                                 let uu____10721 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10721.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10720 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10732,indices) ->
                                                   indices
                                               | uu____10754 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10778  ->
                                                         match uu____10778
                                                         with
                                                         | (x,uu____10784) ->
                                                             let uu____10785
                                                               =
                                                               let uu____10786
                                                                 =
                                                                 let uu____10793
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10793,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10786
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10785)
                                                    env)
                                                in
                                             let uu____10796 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10796 with
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
                                                      let uu____10822 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10838
                                                                 =
                                                                 let uu____10843
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10843,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10838)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10822
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10846 =
                                                      let uu____10847 =
                                                        let uu____10852 =
                                                          let uu____10853 =
                                                            let uu____10858 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10858,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10853
                                                           in
                                                        (out, uu____10852)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10847
                                                       in
                                                    (uu____10846,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10602 with
                    | (data_ax,decls) ->
                        let uu____10871 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10871 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10882 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10882 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10886 =
                                 let uu____10893 =
                                   let uu____10894 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____10895 =
                                     let uu____10906 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10921 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10906,
                                       uu____10921)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____10894 uu____10895
                                    in
                                 let uu____10936 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10893,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10936)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10886
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10939 =
            let uu____10952 =
              let uu____10953 = FStar_Syntax_Subst.compress k  in
              uu____10953.FStar_Syntax_Syntax.n  in
            match uu____10952 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10998 -> (tps, k)  in
          (match uu____10939 with
           | (formals,res) ->
               let uu____11021 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11021 with
                | (formals1,res1) ->
                    let uu____11032 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____11032 with
                     | (vars,guards,env',binder_decls,uu____11057) ->
                         let arity = FStar_List.length vars  in
                         let uu____11071 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11071 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11094 =
                                  let uu____11101 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11101)  in
                                FStar_SMTEncoding_Util.mkApp uu____11094  in
                              let uu____11110 =
                                let tname_decl =
                                  let uu____11120 =
                                    let uu____11121 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11153  ->
                                              match uu____11153 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11166 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11121,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11166, false)
                                     in
                                  constructor_or_logic_type_decl uu____11120
                                   in
                                let uu____11175 =
                                  match vars with
                                  | [] ->
                                      let uu____11188 =
                                        let uu____11189 =
                                          let uu____11192 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____11192
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11189
                                         in
                                      ([], uu____11188)
                                  | uu____11203 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11212 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11212
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11226 =
                                          let uu____11233 =
                                            let uu____11234 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____11235 =
                                              let uu____11250 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11250)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____11234 uu____11235
                                             in
                                          (uu____11233,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11226
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11175 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____11110 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11290 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11290 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11308 =
                                               let uu____11309 =
                                                 let uu____11316 =
                                                   let uu____11317 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11317
                                                    in
                                                 (uu____11316,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11309
                                                in
                                             [uu____11308]
                                           else []  in
                                         let uu____11321 =
                                           let uu____11324 =
                                             let uu____11327 =
                                               let uu____11328 =
                                                 let uu____11335 =
                                                   let uu____11336 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11337 =
                                                     let uu____11348 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11348)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11336 uu____11337
                                                    in
                                                 (uu____11335,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11328
                                                in
                                             [uu____11327]  in
                                           FStar_List.append karr uu____11324
                                            in
                                         FStar_List.append decls1 uu____11321
                                      in
                                   let aux =
                                     let uu____11364 =
                                       let uu____11367 =
                                         inversion_axioms tapp vars  in
                                       let uu____11370 =
                                         let uu____11373 =
                                           let uu____11374 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11374 env2
                                             tapp vars
                                            in
                                         [uu____11373]  in
                                       FStar_List.append uu____11367
                                         uu____11370
                                        in
                                     FStar_List.append kindingAx uu____11364
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11381,uu____11382,uu____11383,uu____11384,uu____11385)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11393,t,uu____11395,n_tps,uu____11397) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11405 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11405 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11445 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11445 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11466 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11466 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11480 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11480 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11550 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11550,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11552 =
                                  let uu____11571 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11571, true)
                                   in
                                let uu____11580 =
                                  let uu____11603 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____11603
                                   in
                                FStar_All.pipe_right uu____11552 uu____11580
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
                              let uu____11634 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11634 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11646::uu____11647 ->
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
                                         let uu____11692 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____11693 =
                                           let uu____11704 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11704)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11692 uu____11693
                                     | uu____11729 -> tok_typing  in
                                   let uu____11738 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11738 with
                                    | (vars',guards',env'',decls_formals,uu____11763)
                                        ->
                                        let uu____11776 =
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
                                        (match uu____11776 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11807 ->
                                                   let uu____11814 =
                                                     let uu____11815 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11815
                                                      in
                                                   [uu____11814]
                                                in
                                             let encode_elim uu____11827 =
                                               let uu____11828 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11828 with
                                               | (head1,args) ->
                                                   let uu____11871 =
                                                     let uu____11872 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11872.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11871 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11882;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11883;_},uu____11884)
                                                        ->
                                                        let uu____11889 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11889
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11902
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11902
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
                                                                    uu____11951
                                                                    ->
                                                                    let uu____11952
                                                                    =
                                                                    let uu____11957
                                                                    =
                                                                    let uu____11958
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11958
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11957)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11952
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11974
                                                                    =
                                                                    let uu____11975
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11975
                                                                     in
                                                                    if
                                                                    uu____11974
                                                                    then
                                                                    let uu____11988
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11988]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11990
                                                                    =
                                                                    let uu____12003
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12053
                                                                     ->
                                                                    fun
                                                                    uu____12054
                                                                     ->
                                                                    match 
                                                                    (uu____12053,
                                                                    uu____12054)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12149
                                                                    =
                                                                    let uu____12156
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12156
                                                                     in
                                                                    (match uu____12149
                                                                    with
                                                                    | 
                                                                    (uu____12169,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12177
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12177
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12179
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12179
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
                                                                    uu____12003
                                                                     in
                                                                  (match uu____11990
                                                                   with
                                                                   | 
                                                                   (uu____12194,arg_vars,elim_eqns_or_guards,uu____12197)
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
                                                                    let uu____12225
                                                                    =
                                                                    let uu____12232
                                                                    =
                                                                    let uu____12233
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12234
                                                                    =
                                                                    let uu____12245
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12256
                                                                    =
                                                                    let uu____12257
                                                                    =
                                                                    let uu____12262
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12262)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12257
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12245,
                                                                    uu____12256)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12233
                                                                    uu____12234
                                                                     in
                                                                    (uu____12232,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12225
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12280
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12280
                                                                    then
                                                                    let x =
                                                                    let uu____12286
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12286,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12288
                                                                    =
                                                                    let uu____12295
                                                                    =
                                                                    let uu____12296
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12297
                                                                    =
                                                                    let uu____12308
                                                                    =
                                                                    let uu____12313
                                                                    =
                                                                    let uu____12316
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12316]
                                                                     in
                                                                    [uu____12313]
                                                                     in
                                                                    let uu____12321
                                                                    =
                                                                    let uu____12322
                                                                    =
                                                                    let uu____12327
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12328
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12327,
                                                                    uu____12328)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12322
                                                                     in
                                                                    (uu____12308,
                                                                    [x],
                                                                    uu____12321)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12296
                                                                    uu____12297
                                                                     in
                                                                    let uu____12347
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12295,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12347)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12288
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12354
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
                                                                    (let uu____12382
                                                                    =
                                                                    let uu____12383
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12383
                                                                    dapp1  in
                                                                    [uu____12382])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12354
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12390
                                                                    =
                                                                    let uu____12397
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12399
                                                                    =
                                                                    let uu____12410
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12421
                                                                    =
                                                                    let uu____12422
                                                                    =
                                                                    let uu____12427
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12427)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12422
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12410,
                                                                    uu____12421)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12398
                                                                    uu____12399
                                                                     in
                                                                    (uu____12397,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12390)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12447 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12447
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12460
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12460
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
                                                                    uu____12509
                                                                    ->
                                                                    let uu____12510
                                                                    =
                                                                    let uu____12515
                                                                    =
                                                                    let uu____12516
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12516
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12515)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12510
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12532
                                                                    =
                                                                    let uu____12533
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12533
                                                                     in
                                                                    if
                                                                    uu____12532
                                                                    then
                                                                    let uu____12546
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12546]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12548
                                                                    =
                                                                    let uu____12561
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12611
                                                                     ->
                                                                    fun
                                                                    uu____12612
                                                                     ->
                                                                    match 
                                                                    (uu____12611,
                                                                    uu____12612)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12707
                                                                    =
                                                                    let uu____12714
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12714
                                                                     in
                                                                    (match uu____12707
                                                                    with
                                                                    | 
                                                                    (uu____12727,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12735
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12735
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12737
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12737
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
                                                                    uu____12561
                                                                     in
                                                                  (match uu____12548
                                                                   with
                                                                   | 
                                                                   (uu____12752,arg_vars,elim_eqns_or_guards,uu____12755)
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
                                                                    let uu____12783
                                                                    =
                                                                    let uu____12790
                                                                    =
                                                                    let uu____12791
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12792
                                                                    =
                                                                    let uu____12803
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12814
                                                                    =
                                                                    let uu____12815
                                                                    =
                                                                    let uu____12820
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12820)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12815
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12803,
                                                                    uu____12814)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12791
                                                                    uu____12792
                                                                     in
                                                                    (uu____12790,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12783
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12838
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12838
                                                                    then
                                                                    let x =
                                                                    let uu____12844
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12844,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12846
                                                                    =
                                                                    let uu____12853
                                                                    =
                                                                    let uu____12854
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12855
                                                                    =
                                                                    let uu____12866
                                                                    =
                                                                    let uu____12871
                                                                    =
                                                                    let uu____12874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12874]
                                                                     in
                                                                    [uu____12871]
                                                                     in
                                                                    let uu____12879
                                                                    =
                                                                    let uu____12880
                                                                    =
                                                                    let uu____12885
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12886
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12885,
                                                                    uu____12886)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12880
                                                                     in
                                                                    (uu____12866,
                                                                    [x],
                                                                    uu____12879)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12854
                                                                    uu____12855
                                                                     in
                                                                    let uu____12905
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12853,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12905)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12846
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12912
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
                                                                    (let uu____12940
                                                                    =
                                                                    let uu____12941
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12941
                                                                    dapp1  in
                                                                    [uu____12940])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12912
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12948
                                                                    =
                                                                    let uu____12955
                                                                    =
                                                                    let uu____12956
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12957
                                                                    =
                                                                    let uu____12968
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12979
                                                                    =
                                                                    let uu____12980
                                                                    =
                                                                    let uu____12985
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12985)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12980
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12968,
                                                                    uu____12979)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12956
                                                                    uu____12957
                                                                     in
                                                                    (uu____12955,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12948)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____13004 ->
                                                        ((let uu____13006 =
                                                            let uu____13011 =
                                                              let uu____13012
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____13013
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____13012
                                                                uu____13013
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____13011)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____13006);
                                                         ([], [])))
                                                in
                                             let uu____13018 = encode_elim ()
                                                in
                                             (match uu____13018 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____13038 =
                                                      let uu____13041 =
                                                        let uu____13044 =
                                                          let uu____13047 =
                                                            let uu____13050 =
                                                              let uu____13051
                                                                =
                                                                let uu____13062
                                                                  =
                                                                  let uu____13065
                                                                    =
                                                                    let uu____13066
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____13066
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____13065
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____13062)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____13051
                                                               in
                                                            [uu____13050]  in
                                                          let uu____13071 =
                                                            let uu____13074 =
                                                              let uu____13077
                                                                =
                                                                let uu____13080
                                                                  =
                                                                  let uu____13083
                                                                    =
                                                                    let uu____13086
                                                                    =
                                                                    let uu____13089
                                                                    =
                                                                    let uu____13090
                                                                    =
                                                                    let uu____13097
                                                                    =
                                                                    let uu____13098
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13099
                                                                    =
                                                                    let uu____13110
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____13110)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13098
                                                                    uu____13099
                                                                     in
                                                                    (uu____13097,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13090
                                                                     in
                                                                    let uu____13123
                                                                    =
                                                                    let uu____13126
                                                                    =
                                                                    let uu____13127
                                                                    =
                                                                    let uu____13134
                                                                    =
                                                                    let uu____13135
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13136
                                                                    =
                                                                    let uu____13147
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____13158
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____13147,
                                                                    uu____13158)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13135
                                                                    uu____13136
                                                                     in
                                                                    (uu____13134,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13127
                                                                     in
                                                                    [uu____13126]
                                                                     in
                                                                    uu____13089
                                                                    ::
                                                                    uu____13123
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____13086
                                                                     in
                                                                  FStar_List.append
                                                                    uu____13083
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____13080
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____13077
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____13074
                                                             in
                                                          FStar_List.append
                                                            uu____13047
                                                            uu____13071
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____13044
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____13041
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____13038
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
           (fun uu____13204  ->
              fun se  ->
                match uu____13204 with
                | (g,env1) ->
                    let uu____13224 = encode_sigelt env1 se  in
                    (match uu____13224 with
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
      let encode_binding b uu____13289 =
        match uu____13289 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____13321 ->
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
                 ((let uu____13327 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13327
                   then
                     let uu____13328 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13329 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13330 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13328 uu____13329 uu____13330
                   else ());
                  (let uu____13332 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13332 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13348 =
                         let uu____13355 =
                           let uu____13356 =
                             let uu____13357 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13357
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13356  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13355
                          in
                       (match uu____13348 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13373 = FStar_Options.log_queries ()
                                 in
                              if uu____13373
                              then
                                let uu____13376 =
                                  let uu____13377 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13378 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13379 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13377 uu____13378 uu____13379
                                   in
                                FStar_Pervasives_Native.Some uu____13376
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____13395,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13409 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13409 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____13432,se,uu____13434) ->
                 let uu____13439 = encode_sigelt env1 se  in
                 (match uu____13439 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____13456,se) ->
                 let uu____13462 = encode_sigelt env1 se  in
                 (match uu____13462 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13479 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13479 with | (uu____13502,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13517 'Auu____13518 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13517,'Auu____13518)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13587  ->
              match uu____13587 with
              | (l,uu____13599,uu____13600) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13646  ->
              match uu____13646 with
              | (l,uu____13660,uu____13661) ->
                  let uu____13670 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13671 =
                    let uu____13674 =
                      let uu____13675 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13675  in
                    [uu____13674]  in
                  uu____13670 :: uu____13671))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13702 =
      let uu____13705 =
        let uu____13706 = FStar_Util.psmap_empty ()  in
        let uu____13721 = FStar_Util.psmap_empty ()  in
        let uu____13724 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13727 =
          let uu____13728 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13728 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13706;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13721;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13724;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13727;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13705]  in
    FStar_ST.op_Colon_Equals last_env uu____13702
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13766 = FStar_ST.op_Bang last_env  in
      match uu____13766 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13797 ->
          let uu___94_13800 = e  in
          let uu____13801 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___94_13800.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___94_13800.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___94_13800.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___94_13800.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___94_13800.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___94_13800.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___94_13800.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___94_13800.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13801;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___94_13800.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13807 = FStar_ST.op_Bang last_env  in
    match uu____13807 with
    | [] -> failwith "Empty env stack"
    | uu____13837::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13872  ->
    let uu____13873 = FStar_ST.op_Bang last_env  in
    match uu____13873 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
        let top =
          let uu___95_13911 = hd1  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___95_13911.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___95_13911.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___95_13911.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___95_13911.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___95_13911.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = refs;
            FStar_SMTEncoding_Env.nolabels =
              (uu___95_13911.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___95_13911.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___95_13911.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___95_13911.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___95_13911.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13943  ->
    let uu____13944 = FStar_ST.op_Bang last_env  in
    match uu____13944 with
    | [] -> failwith "Popping an empty stack"
    | uu____13974::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> unit) =
  fun msg  ->
    push_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.push ();
    FStar_SMTEncoding_Z3.push msg
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    pop_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.pop ();
    FStar_SMTEncoding_Z3.pop msg
  
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
        | (uu____14056::uu____14057,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___96_14065 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___96_14065.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___96_14065.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___96_14065.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____14066 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____14085 =
        let uu____14088 =
          let uu____14089 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____14089  in
        let uu____14090 = open_fact_db_tags env  in uu____14088 ::
          uu____14090
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____14085
  
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
      let uu____14116 = encode_sigelt env se  in
      match uu____14116 with
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
        let uu____14158 = FStar_Options.log_queries ()  in
        if uu____14158
        then
          let uu____14161 =
            let uu____14162 =
              let uu____14163 =
                let uu____14164 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14164 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14163  in
            FStar_SMTEncoding_Term.Caption uu____14162  in
          uu____14161 :: decls
        else decls  in
      (let uu____14175 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14175
       then
         let uu____14176 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14176
       else ());
      (let env =
         let uu____14179 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14179 tcenv  in
       let uu____14180 = encode_top_level_facts env se  in
       match uu____14180 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14194 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14194)))
  
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
      (let uu____14210 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14210
       then
         let uu____14211 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14211
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14250  ->
                 fun se  ->
                   match uu____14250 with
                   | (g,env2) ->
                       let uu____14270 = encode_top_level_facts env2 se  in
                       (match uu____14270 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14293 =
         encode_signature
           (let uu___97_14302 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___97_14302.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___97_14302.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___97_14302.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___97_14302.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___97_14302.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___97_14302.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___97_14302.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___97_14302.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___97_14302.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___97_14302.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14293 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14321 = FStar_Options.log_queries ()  in
             if uu____14321
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___98_14329 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___98_14329.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___98_14329.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___98_14329.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___98_14329.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___98_14329.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___98_14329.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___98_14329.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___98_14329.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___98_14329.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___98_14329.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14331 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14331
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
        (let uu____14389 =
           let uu____14390 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14390.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14389);
        (let env =
           let uu____14392 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14392 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____14404 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____14441 = aux rest  in
                 (match uu____14441 with
                  | (out,rest1) ->
                      let t =
                        let uu____14471 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14471 with
                        | FStar_Pervasives_Native.Some uu____14476 ->
                            let uu____14477 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14477
                              x.FStar_Syntax_Syntax.sort
                        | uu____14478 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14482 =
                        let uu____14485 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___99_14488 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___99_14488.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___99_14488.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14485 :: out  in
                      (uu____14482, rest1))
             | uu____14493 -> ([], bindings1)  in
           let uu____14500 = aux bindings  in
           match uu____14500 with
           | (closing,bindings1) ->
               let uu____14525 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14525, bindings1)
            in
         match uu____14404 with
         | (q1,bindings1) ->
             let uu____14548 =
               let uu____14553 =
                 FStar_List.filter
                   (fun uu___81_14558  ->
                      match uu___81_14558 with
                      | FStar_TypeChecker_Env.Binding_sig uu____14559 ->
                          false
                      | uu____14566 -> true) bindings1
                  in
               encode_env_bindings env uu____14553  in
             (match uu____14548 with
              | (env_decls,env1) ->
                  ((let uu____14584 =
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
                    if uu____14584
                    then
                      let uu____14585 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14585
                    else ());
                   (let uu____14587 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14587 with
                    | (phi,qdecls) ->
                        let uu____14608 =
                          let uu____14613 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14613 phi
                           in
                        (match uu____14608 with
                         | (labels,phi1) ->
                             let uu____14630 = encode_labels labels  in
                             (match uu____14630 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14667 =
                                      let uu____14674 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14675 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14674,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14675)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14667
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
  