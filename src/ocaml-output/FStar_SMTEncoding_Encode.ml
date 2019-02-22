open Prims
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
  let uu____139 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort
     in
  match uu____139 with
  | (asym,a) ->
      let uu____150 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____150 with
       | (xsym,x) ->
           let uu____161 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____161 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____239 =
                      let uu____251 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort)
                         in
                      (x1, uu____251, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____239  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____271 =
                      let uu____279 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____279)  in
                    FStar_SMTEncoding_Util.mkApp uu____271  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____298 =
                    let uu____301 =
                      let uu____304 =
                        let uu____307 =
                          let uu____308 =
                            let uu____316 =
                              let uu____317 =
                                let uu____328 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____328)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____317
                               in
                            (uu____316, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____308  in
                        let uu____340 =
                          let uu____343 =
                            let uu____344 =
                              let uu____352 =
                                let uu____353 =
                                  let uu____364 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____364)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____353
                                 in
                              (uu____352,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____344  in
                          [uu____343]  in
                        uu____307 :: uu____340  in
                      xtok_decl :: uu____304  in
                    xname_decl :: uu____301  in
                  (xtok1, (FStar_List.length vars), uu____298)  in
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
                  let uu____534 =
                    let uu____555 =
                      let uu____574 =
                        let uu____575 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____575
                         in
                      quant axy uu____574  in
                    (FStar_Parser_Const.op_Eq, uu____555)  in
                  let uu____592 =
                    let uu____615 =
                      let uu____636 =
                        let uu____655 =
                          let uu____656 =
                            let uu____657 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____657  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____656
                           in
                        quant axy uu____655  in
                      (FStar_Parser_Const.op_notEq, uu____636)  in
                    let uu____674 =
                      let uu____697 =
                        let uu____718 =
                          let uu____737 =
                            let uu____738 =
                              let uu____739 =
                                let uu____744 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____745 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____744, uu____745)  in
                              FStar_SMTEncoding_Util.mkLT uu____739  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____738
                             in
                          quant xy uu____737  in
                        (FStar_Parser_Const.op_LT, uu____718)  in
                      let uu____762 =
                        let uu____785 =
                          let uu____806 =
                            let uu____825 =
                              let uu____826 =
                                let uu____827 =
                                  let uu____832 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____833 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____832, uu____833)  in
                                FStar_SMTEncoding_Util.mkLTE uu____827  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____826
                               in
                            quant xy uu____825  in
                          (FStar_Parser_Const.op_LTE, uu____806)  in
                        let uu____850 =
                          let uu____873 =
                            let uu____894 =
                              let uu____913 =
                                let uu____914 =
                                  let uu____915 =
                                    let uu____920 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____921 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____920, uu____921)  in
                                  FStar_SMTEncoding_Util.mkGT uu____915  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____914
                                 in
                              quant xy uu____913  in
                            (FStar_Parser_Const.op_GT, uu____894)  in
                          let uu____938 =
                            let uu____961 =
                              let uu____982 =
                                let uu____1001 =
                                  let uu____1002 =
                                    let uu____1003 =
                                      let uu____1008 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1009 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1008, uu____1009)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1003
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1002
                                   in
                                quant xy uu____1001  in
                              (FStar_Parser_Const.op_GTE, uu____982)  in
                            let uu____1026 =
                              let uu____1049 =
                                let uu____1070 =
                                  let uu____1089 =
                                    let uu____1090 =
                                      let uu____1091 =
                                        let uu____1096 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1097 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1096, uu____1097)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1091
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1090
                                     in
                                  quant xy uu____1089  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1070)
                                 in
                              let uu____1114 =
                                let uu____1137 =
                                  let uu____1158 =
                                    let uu____1177 =
                                      let uu____1178 =
                                        let uu____1179 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1179
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1178
                                       in
                                    quant qx uu____1177  in
                                  (FStar_Parser_Const.op_Minus, uu____1158)
                                   in
                                let uu____1196 =
                                  let uu____1219 =
                                    let uu____1240 =
                                      let uu____1259 =
                                        let uu____1260 =
                                          let uu____1261 =
                                            let uu____1266 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1267 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1266, uu____1267)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1261
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1260
                                         in
                                      quant xy uu____1259  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1240)
                                     in
                                  let uu____1284 =
                                    let uu____1307 =
                                      let uu____1328 =
                                        let uu____1347 =
                                          let uu____1348 =
                                            let uu____1349 =
                                              let uu____1354 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1355 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1354, uu____1355)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1349
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1348
                                           in
                                        quant xy uu____1347  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1328)
                                       in
                                    let uu____1372 =
                                      let uu____1395 =
                                        let uu____1416 =
                                          let uu____1435 =
                                            let uu____1436 =
                                              let uu____1437 =
                                                let uu____1442 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1443 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1442, uu____1443)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1437
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1436
                                             in
                                          quant xy uu____1435  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1416)
                                         in
                                      let uu____1460 =
                                        let uu____1483 =
                                          let uu____1504 =
                                            let uu____1523 =
                                              let uu____1524 =
                                                let uu____1525 =
                                                  let uu____1530 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1531 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1530, uu____1531)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1525
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1524
                                               in
                                            quant xy uu____1523  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1504)
                                           in
                                        let uu____1548 =
                                          let uu____1571 =
                                            let uu____1592 =
                                              let uu____1611 =
                                                let uu____1612 =
                                                  let uu____1613 =
                                                    let uu____1618 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1619 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1618, uu____1619)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1613
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1612
                                                 in
                                              quant xy uu____1611  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1592)
                                             in
                                          let uu____1636 =
                                            let uu____1659 =
                                              let uu____1680 =
                                                let uu____1699 =
                                                  let uu____1700 =
                                                    let uu____1701 =
                                                      let uu____1706 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1707 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1706,
                                                        uu____1707)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1701
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1700
                                                   in
                                                quant xy uu____1699  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1680)
                                               in
                                            let uu____1724 =
                                              let uu____1747 =
                                                let uu____1768 =
                                                  let uu____1787 =
                                                    let uu____1788 =
                                                      let uu____1789 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1789
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1788
                                                     in
                                                  quant qx uu____1787  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1768)
                                                 in
                                              [uu____1747]  in
                                            uu____1659 :: uu____1724  in
                                          uu____1571 :: uu____1636  in
                                        uu____1483 :: uu____1548  in
                                      uu____1395 :: uu____1460  in
                                    uu____1307 :: uu____1372  in
                                  uu____1219 :: uu____1284  in
                                uu____1137 :: uu____1196  in
                              uu____1049 :: uu____1114  in
                            uu____961 :: uu____1026  in
                          uu____873 :: uu____938  in
                        uu____785 :: uu____850  in
                      uu____697 :: uu____762  in
                    uu____615 :: uu____674  in
                  uu____534 :: uu____592  in
                let mk1 l v1 =
                  let uu____2148 =
                    let uu____2160 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2250  ->
                              match uu____2250 with
                              | (l',uu____2271) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2160
                      (FStar_Option.map
                         (fun uu____2370  ->
                            match uu____2370 with
                            | (uu____2398,b) ->
                                let uu____2432 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2432 v1))
                     in
                  FStar_All.pipe_right uu____2148 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2515  ->
                          match uu____2515 with
                          | (l',uu____2536) -> FStar_Ident.lid_equals l l'))
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
          let uu____2610 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2610 with
          | (xxsym,xx) ->
              let uu____2621 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2621 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2637 =
                     let uu____2645 =
                       let uu____2646 =
                         let uu____2657 =
                           let uu____2658 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort)
                              in
                           let uu____2668 =
                             let uu____2679 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort)
                                in
                             uu____2679 :: vars  in
                           uu____2658 :: uu____2668  in
                         let uu____2705 =
                           let uu____2706 =
                             let uu____2711 =
                               let uu____2712 =
                                 let uu____2717 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2717)  in
                               FStar_SMTEncoding_Util.mkEq uu____2712  in
                             (xx_has_type, uu____2711)  in
                           FStar_SMTEncoding_Util.mkImp uu____2706  in
                         ([[xx_has_type]], uu____2657, uu____2705)  in
                       FStar_SMTEncoding_Term.mkForall rng uu____2646  in
                     let uu____2730 =
                       let uu____2732 =
                         let uu____2734 =
                           let uu____2736 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2736  in
                         Prims.strcat module_name uu____2734  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2732
                        in
                     (uu____2645, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2730)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2637)
  
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
    let uu____2792 =
      let uu____2794 = FStar_TypeChecker_Env.current_module env  in
      FStar_Ident.string_of_lid uu____2794  in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2792  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____2816 =
      let uu____2817 =
        let uu____2825 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2825, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2817  in
    let uu____2830 =
      let uu____2833 =
        let uu____2834 =
          let uu____2842 =
            let uu____2843 =
              let uu____2854 =
                let uu____2855 =
                  let uu____2860 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2860)  in
                FStar_SMTEncoding_Util.mkImp uu____2855  in
              ([[typing_pred]], [xx], uu____2854)  in
            let uu____2885 =
              let uu____2900 = FStar_TypeChecker_Env.get_range env  in
              let uu____2901 = mkForall_fuel1 env  in uu____2901 uu____2900
               in
            uu____2885 uu____2843  in
          (uu____2842, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2834  in
      [uu____2833]  in
    uu____2816 :: uu____2830  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2948 =
      let uu____2949 =
        let uu____2957 =
          let uu____2958 = FStar_TypeChecker_Env.get_range env  in
          let uu____2959 =
            let uu____2970 =
              let uu____2975 =
                let uu____2978 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2978]  in
              [uu____2975]  in
            let uu____2983 =
              let uu____2984 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2984 tt  in
            (uu____2970, [bb], uu____2983)  in
          FStar_SMTEncoding_Term.mkForall uu____2958 uu____2959  in
        (uu____2957, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2949  in
    let uu____3009 =
      let uu____3012 =
        let uu____3013 =
          let uu____3021 =
            let uu____3022 =
              let uu____3033 =
                let uu____3034 =
                  let uu____3039 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3039)  in
                FStar_SMTEncoding_Util.mkImp uu____3034  in
              ([[typing_pred]], [xx], uu____3033)  in
            let uu____3066 =
              let uu____3081 = FStar_TypeChecker_Env.get_range env  in
              let uu____3082 = mkForall_fuel1 env  in uu____3082 uu____3081
               in
            uu____3066 uu____3022  in
          (uu____3021, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3013  in
      [uu____3012]  in
    uu____2948 :: uu____3009  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3125 =
        let uu____3126 =
          let uu____3132 =
            FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid  in
          (uu____3132, FStar_SMTEncoding_Term.Term_sort)  in
        FStar_SMTEncoding_Term.mk_fv uu____3126  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3125  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3146 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3146  in
    let uu____3151 =
      let uu____3152 =
        let uu____3160 =
          let uu____3161 = FStar_TypeChecker_Env.get_range env  in
          let uu____3162 =
            let uu____3173 =
              let uu____3178 =
                let uu____3181 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3181]  in
              [uu____3178]  in
            let uu____3186 =
              let uu____3187 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3187 tt  in
            (uu____3173, [bb], uu____3186)  in
          FStar_SMTEncoding_Term.mkForall uu____3161 uu____3162  in
        (uu____3160, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3152  in
    let uu____3212 =
      let uu____3215 =
        let uu____3216 =
          let uu____3224 =
            let uu____3225 =
              let uu____3236 =
                let uu____3237 =
                  let uu____3242 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3242)  in
                FStar_SMTEncoding_Util.mkImp uu____3237  in
              ([[typing_pred]], [xx], uu____3236)  in
            let uu____3269 =
              let uu____3284 = FStar_TypeChecker_Env.get_range env  in
              let uu____3285 = mkForall_fuel1 env  in uu____3285 uu____3284
               in
            uu____3269 uu____3225  in
          (uu____3224, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3216  in
      let uu____3307 =
        let uu____3310 =
          let uu____3311 =
            let uu____3319 =
              let uu____3320 =
                let uu____3331 =
                  let uu____3332 =
                    let uu____3337 =
                      let uu____3338 =
                        let uu____3341 =
                          let uu____3344 =
                            let uu____3347 =
                              let uu____3348 =
                                let uu____3353 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3354 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3353, uu____3354)  in
                              FStar_SMTEncoding_Util.mkGT uu____3348  in
                            let uu____3356 =
                              let uu____3359 =
                                let uu____3360 =
                                  let uu____3365 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3366 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3365, uu____3366)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3360  in
                              let uu____3368 =
                                let uu____3371 =
                                  let uu____3372 =
                                    let uu____3377 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3378 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3377, uu____3378)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3372  in
                                [uu____3371]  in
                              uu____3359 :: uu____3368  in
                            uu____3347 :: uu____3356  in
                          typing_pred_y :: uu____3344  in
                        typing_pred :: uu____3341  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3338  in
                    (uu____3337, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3332  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3331)
                 in
              let uu____3411 =
                let uu____3426 = FStar_TypeChecker_Env.get_range env  in
                let uu____3427 = mkForall_fuel1 env  in uu____3427 uu____3426
                 in
              uu____3411 uu____3320  in
            (uu____3319,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3311  in
        [uu____3310]  in
      uu____3215 :: uu____3307  in
    uu____3151 :: uu____3212  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort)
       in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3474 =
      let uu____3475 =
        let uu____3483 =
          let uu____3484 = FStar_TypeChecker_Env.get_range env  in
          let uu____3485 =
            let uu____3496 =
              let uu____3501 =
                let uu____3504 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3504]  in
              [uu____3501]  in
            let uu____3509 =
              let uu____3510 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3510 tt  in
            (uu____3496, [bb], uu____3509)  in
          FStar_SMTEncoding_Term.mkForall uu____3484 uu____3485  in
        (uu____3483, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3475  in
    let uu____3535 =
      let uu____3538 =
        let uu____3539 =
          let uu____3547 =
            let uu____3548 =
              let uu____3559 =
                let uu____3560 =
                  let uu____3565 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3565)  in
                FStar_SMTEncoding_Util.mkImp uu____3560  in
              ([[typing_pred]], [xx], uu____3559)  in
            let uu____3592 =
              let uu____3607 = FStar_TypeChecker_Env.get_range env  in
              let uu____3608 = mkForall_fuel1 env  in uu____3608 uu____3607
               in
            uu____3592 uu____3548  in
          (uu____3547, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3539  in
      [uu____3538]  in
    uu____3474 :: uu____3535  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3655 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3655]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3685 =
      let uu____3686 =
        let uu____3694 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3694, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3686  in
    [uu____3685]  in
  let mk_and_interp env conj uu____3717 =
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
    let uu____3746 =
      let uu____3747 =
        let uu____3755 =
          let uu____3756 = FStar_TypeChecker_Env.get_range env  in
          let uu____3757 =
            let uu____3768 =
              let uu____3769 =
                let uu____3774 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3774, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3769  in
            ([[l_and_a_b]], [aa; bb], uu____3768)  in
          FStar_SMTEncoding_Term.mkForall uu____3756 uu____3757  in
        (uu____3755, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3747  in
    [uu____3746]  in
  let mk_or_interp env disj uu____3829 =
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
    let uu____3858 =
      let uu____3859 =
        let uu____3867 =
          let uu____3868 = FStar_TypeChecker_Env.get_range env  in
          let uu____3869 =
            let uu____3880 =
              let uu____3881 =
                let uu____3886 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3886, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3881  in
            ([[l_or_a_b]], [aa; bb], uu____3880)  in
          FStar_SMTEncoding_Term.mkForall uu____3868 uu____3869  in
        (uu____3867, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3859  in
    [uu____3858]  in
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
    let uu____3964 =
      let uu____3965 =
        let uu____3973 =
          let uu____3974 = FStar_TypeChecker_Env.get_range env  in
          let uu____3975 =
            let uu____3986 =
              let uu____3987 =
                let uu____3992 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3992, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3987  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3986)  in
          FStar_SMTEncoding_Term.mkForall uu____3974 uu____3975  in
        (uu____3973, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3965  in
    [uu____3964]  in
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
    let uu____4082 =
      let uu____4083 =
        let uu____4091 =
          let uu____4092 = FStar_TypeChecker_Env.get_range env  in
          let uu____4093 =
            let uu____4104 =
              let uu____4105 =
                let uu____4110 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4110, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4105  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4104)  in
          FStar_SMTEncoding_Term.mkForall uu____4092 uu____4093  in
        (uu____4091, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4083  in
    [uu____4082]  in
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
    let uu____4210 =
      let uu____4211 =
        let uu____4219 =
          let uu____4220 = FStar_TypeChecker_Env.get_range env  in
          let uu____4221 =
            let uu____4232 =
              let uu____4233 =
                let uu____4238 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____4238, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4233  in
            ([[l_imp_a_b]], [aa; bb], uu____4232)  in
          FStar_SMTEncoding_Term.mkForall uu____4220 uu____4221  in
        (uu____4219, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4211  in
    [uu____4210]  in
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
    let uu____4322 =
      let uu____4323 =
        let uu____4331 =
          let uu____4332 = FStar_TypeChecker_Env.get_range env  in
          let uu____4333 =
            let uu____4344 =
              let uu____4345 =
                let uu____4350 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4350, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4345  in
            ([[l_iff_a_b]], [aa; bb], uu____4344)  in
          FStar_SMTEncoding_Term.mkForall uu____4332 uu____4333  in
        (uu____4331, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4323  in
    [uu____4322]  in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort)
       in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4421 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4421  in
    let uu____4426 =
      let uu____4427 =
        let uu____4435 =
          let uu____4436 = FStar_TypeChecker_Env.get_range env  in
          let uu____4437 =
            let uu____4448 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4448)  in
          FStar_SMTEncoding_Term.mkForall uu____4436 uu____4437  in
        (uu____4435, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4427  in
    [uu____4426]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4501 =
      let uu____4502 =
        let uu____4510 =
          let uu____4511 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4511 range_ty  in
        let uu____4512 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4510, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4512)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4502  in
    [uu____4501]  in
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
        let uu____4558 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4558 x1 t  in
      let uu____4560 = FStar_TypeChecker_Env.get_range env  in
      let uu____4561 =
        let uu____4572 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4572)  in
      FStar_SMTEncoding_Term.mkForall uu____4560 uu____4561  in
    let uu____4597 =
      let uu____4598 =
        let uu____4606 =
          let uu____4607 = FStar_TypeChecker_Env.get_range env  in
          let uu____4608 =
            let uu____4619 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4619)  in
          FStar_SMTEncoding_Term.mkForall uu____4607 uu____4608  in
        (uu____4606,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4598  in
    [uu____4597]  in
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
    let uu____4680 =
      let uu____4681 =
        let uu____4689 =
          let uu____4690 = FStar_TypeChecker_Env.get_range env  in
          let uu____4691 =
            let uu____4707 =
              let uu____4708 =
                let uu____4713 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4714 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4713, uu____4714)  in
              FStar_SMTEncoding_Util.mkAnd uu____4708  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4707)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4690 uu____4691  in
        (uu____4689,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4681  in
    [uu____4680]  in
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
          let uu____5244 =
            FStar_Util.find_opt
              (fun uu____5282  ->
                 match uu____5282 with
                 | (l,uu____5298) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5244 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____5341,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5402 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5402 with
        | (form,decls) ->
            let uu____5411 =
              let uu____5414 =
                let uu____5417 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.strcat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____5417]  in
              FStar_All.pipe_right uu____5414
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____5411
  
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
              let uu____5476 =
                ((let uu____5480 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5480) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5476
              then
                let arg_sorts =
                  let uu____5492 =
                    let uu____5493 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5493.FStar_Syntax_Syntax.n  in
                  match uu____5492 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5499) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5537  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5544 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5546 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5546 with
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
                    let uu____5582 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____5582, env1)
              else
                (let uu____5587 = prims.is lid  in
                 if uu____5587
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5596 = prims.mk lid vname  in
                   match uu____5596 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____5620 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____5620, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5629 =
                      let uu____5648 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5648 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5676 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5676
                            then
                              let uu____5681 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___33_5684 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___33_5684.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___33_5684.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___33_5684.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___33_5684.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___33_5684.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___33_5684.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___33_5684.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___33_5684.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___33_5684.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___33_5684.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___33_5684.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___33_5684.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___33_5684.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___33_5684.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___33_5684.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___33_5684.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___33_5684.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___33_5684.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___33_5684.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___33_5684.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___33_5684.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___33_5684.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___33_5684.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___33_5684.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___33_5684.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___33_5684.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___33_5684.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___33_5684.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___33_5684.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___33_5684.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___33_5684.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___33_5684.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___33_5684.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___33_5684.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___33_5684.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___33_5684.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___33_5684.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___33_5684.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___33_5684.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___33_5684.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___33_5684.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___33_5684.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5681
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5707 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5707)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5629 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___22_5813  ->
                                  match uu___22_5813 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____5817 = FStar_Util.prefix vars
                                         in
                                      (match uu____5817 with
                                       | (uu____5850,xxv) ->
                                           let xx =
                                             let uu____5889 =
                                               let uu____5890 =
                                                 let uu____5896 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____5896,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____5890
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____5889
                                              in
                                           let uu____5899 =
                                             let uu____5900 =
                                               let uu____5908 =
                                                 let uu____5909 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5910 =
                                                   let uu____5921 =
                                                     let uu____5922 =
                                                       let uu____5927 =
                                                         let uu____5928 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____5928
                                                          in
                                                       (vapp, uu____5927)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____5922
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5921)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5909 uu____5910
                                                  in
                                               (uu____5908,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.strcat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5900
                                              in
                                           [uu____5899])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____5943 = FStar_Util.prefix vars
                                         in
                                      (match uu____5943 with
                                       | (uu____5976,xxv) ->
                                           let xx =
                                             let uu____6015 =
                                               let uu____6016 =
                                                 let uu____6022 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv
                                                    in
                                                 (uu____6022,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____6016
                                                in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____6015
                                              in
                                           let f1 =
                                             {
                                               FStar_Syntax_Syntax.ppname = f;
                                               FStar_Syntax_Syntax.index =
                                                 (Prims.parse_int "0");
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
                                           let uu____6033 =
                                             let uu____6034 =
                                               let uu____6042 =
                                                 let uu____6043 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____6044 =
                                                   let uu____6055 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____6055)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____6043 uu____6044
                                                  in
                                               (uu____6042,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.strcat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6034
                                              in
                                           [uu____6033])
                                  | uu____6068 -> []))
                           in
                        let uu____6069 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____6069 with
                         | (vars,guards,env',decls1,uu____6094) ->
                             let uu____6107 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____6120 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____6120, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____6124 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____6124 with
                                    | (g,ds) ->
                                        let uu____6137 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____6137,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____6107 with
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
                                  let should_thunk uu____6160 =
                                    let is_type1 t =
                                      let uu____6168 =
                                        let uu____6169 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6169.FStar_Syntax_Syntax.n  in
                                      match uu____6168 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____6173 -> true
                                      | uu____6175 -> false  in
                                    let is_squash1 t =
                                      let uu____6184 =
                                        FStar_Syntax_Util.head_and_args t  in
                                      match uu____6184 with
                                      | (head1,uu____6203) ->
                                          let uu____6228 =
                                            let uu____6229 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____6229.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6228 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____6234;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____6235;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____6237;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____6238;_};_},uu____6239)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____6247 -> false)
                                       in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____6252 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____6252))
                                       &&
                                       (let uu____6258 = is_squash1 t_norm
                                           in
                                        Prims.op_Negation uu____6258))
                                      &&
                                      (let uu____6261 = is_type1 t_norm  in
                                       Prims.op_Negation uu____6261)
                                     in
                                  let uu____6263 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____6322 -> (false, vars)  in
                                  (match uu____6263 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____6372 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____6372 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____6408 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  let uu____6417 =
                                                    FStar_SMTEncoding_Term.mk_fv
                                                      (vname,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    uu____6417
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____6428 ->
                                                  let uu____6437 =
                                                    let uu____6445 =
                                                      get_vtok ()  in
                                                    (uu____6445, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6437
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____6452 =
                                                let uu____6460 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____6460)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____6452
                                               in
                                            let uu____6474 =
                                              let vname_decl =
                                                let uu____6482 =
                                                  let uu____6494 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort)
                                                     in
                                                  (vname, uu____6494,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____6482
                                                 in
                                              let uu____6505 =
                                                let env2 =
                                                  let uu___34_6511 = env1  in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___34_6511.FStar_SMTEncoding_Env.global_cache)
                                                  }  in
                                                let uu____6512 =
                                                  let uu____6514 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____6514
                                                   in
                                                if uu____6512
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____6505 with
                                              | (tok_typing,decls2) ->
                                                  let uu____6531 =
                                                    match vars1 with
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
                                                        let uu____6557 =
                                                          let uu____6560 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6560
                                                           in
                                                        let uu____6567 =
                                                          let uu____6568 =
                                                            let uu____6571 =
                                                              let uu____6572
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                uu____6572
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____6571
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____6568
                                                           in
                                                        (uu____6557,
                                                          uu____6567)
                                                    | uu____6582 when thunked
                                                        ->
                                                        let uu____6593 =
                                                          FStar_Options.protect_top_level_axioms
                                                            ()
                                                           in
                                                        if uu____6593
                                                        then (decls2, env1)
                                                        else
                                                          (let intro_ambient1
                                                             =
                                                             let t =
                                                               let uu____6608
                                                                 =
                                                                 let uu____6616
                                                                   =
                                                                   let uu____6619
                                                                    =
                                                                    let uu____6622
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (vname,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    true)  in
                                                                    [uu____6622]
                                                                     in
                                                                   FStar_SMTEncoding_Term.mk_Term_unit
                                                                    ::
                                                                    uu____6619
                                                                    in
                                                                 ("FStar.Pervasives.ambient",
                                                                   uu____6616)
                                                                  in
                                                               FStar_SMTEncoding_Term.mkApp
                                                                 uu____6608
                                                                 FStar_Range.dummyRange
                                                                in
                                                             let uu____6630 =
                                                               let uu____6638
                                                                 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   t
                                                                  in
                                                               (uu____6638,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Ambient nullary symbol trigger"),
                                                                 (Prims.strcat
                                                                    "intro_ambient_"
                                                                    vname))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____6630
                                                              in
                                                           let uu____6643 =
                                                             let uu____6646 =
                                                               FStar_All.pipe_right
                                                                 [intro_ambient1]
                                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                                in
                                                             FStar_List.append
                                                               decls2
                                                               uu____6646
                                                              in
                                                           (uu____6643, env1))
                                                    | uu____6655 ->
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
                                                          let uu____6679 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____6680 =
                                                            let uu____6691 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____6691)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____6679
                                                            uu____6680
                                                           in
                                                        let name_tok_corr =
                                                          let uu____6701 =
                                                            let uu____6709 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____6709,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____6701
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
                                                            let uu____6720 =
                                                              let uu____6721
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                 in
                                                              [uu____6721]
                                                               in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____6720
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____6748 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6749 =
                                                              let uu____6760
                                                                =
                                                                let uu____6761
                                                                  =
                                                                  let uu____6766
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____6767
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____6766,
                                                                    uu____6767)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____6761
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____6760)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6748
                                                              uu____6749
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        let uu____6796 =
                                                          let uu____6799 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6799
                                                           in
                                                        (uu____6796, env1)
                                                     in
                                                  (match uu____6531 with
                                                   | (tok_decl,env2) ->
                                                       let uu____6820 =
                                                         let uu____6823 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                                            in
                                                         FStar_List.append
                                                           uu____6823
                                                           tok_decl
                                                          in
                                                       (uu____6820, env2))
                                               in
                                            (match uu____6474 with
                                             | (decls2,env2) ->
                                                 let uu____6842 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____6852 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____6852 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____6867 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____6867, decls)
                                                    in
                                                 (match uu____6842 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____6882 =
                                                          let uu____6890 =
                                                            let uu____6891 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6892 =
                                                              let uu____6903
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____6903)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6891
                                                              uu____6892
                                                             in
                                                          (uu____6890,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6882
                                                         in
                                                      let freshness =
                                                        let uu____6919 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____6919
                                                        then
                                                          let uu____6927 =
                                                            let uu____6928 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6929 =
                                                              let uu____6942
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort)
                                                                 in
                                                              let uu____6949
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____6942,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____6949)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____6928
                                                              uu____6929
                                                             in
                                                          let uu____6955 =
                                                            let uu____6958 =
                                                              let uu____6959
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____6959
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____6958]  in
                                                          uu____6927 ::
                                                            uu____6955
                                                        else []  in
                                                      let g =
                                                        let uu____6965 =
                                                          let uu____6968 =
                                                            let uu____6971 =
                                                              let uu____6974
                                                                =
                                                                let uu____6977
                                                                  =
                                                                  let uu____6980
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1  in
                                                                  typingAx ::
                                                                    uu____6980
                                                                   in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____6977
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____6974
                                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____6971
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6968
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____6965
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
          let uu____7020 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7020 with
          | FStar_Pervasives_Native.None  ->
              let uu____7031 = encode_free_var false env x t t_norm []  in
              (match uu____7031 with
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
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____7094 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7094 with
            | (decls,env1) ->
                let uu____7105 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7105
                then
                  let uu____7112 =
                    let uu____7113 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7113  in
                  (uu____7112, env1)
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
             (fun uu____7169  ->
                fun lb  ->
                  match uu____7169 with
                  | (decls,env1) ->
                      let uu____7189 =
                        let uu____7194 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7194
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7189 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7223 = FStar_Syntax_Util.head_and_args t  in
    match uu____7223 with
    | (hd1,args) ->
        let uu____7267 =
          let uu____7268 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7268.FStar_Syntax_Syntax.n  in
        (match uu____7267 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7274,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7298 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7309 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___35_7317 = en  in
    let uu____7318 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___35_7317.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___35_7317.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___35_7317.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___35_7317.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___35_7317.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___35_7317.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___35_7317.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___35_7317.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___35_7317.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___35_7317.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____7318
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7348  ->
      fun quals  ->
        match uu____7348 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7453 = FStar_Util.first_N nbinders formals  in
              match uu____7453 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7554  ->
                         fun uu____7555  ->
                           match (uu____7554, uu____7555) with
                           | ((formal,uu____7581),(binder,uu____7583)) ->
                               let uu____7604 =
                                 let uu____7611 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7611)  in
                               FStar_Syntax_Syntax.NT uu____7604) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7625 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7666  ->
                              match uu____7666 with
                              | (x,i) ->
                                  let uu____7685 =
                                    let uu___36_7686 = x  in
                                    let uu____7687 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___36_7686.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___36_7686.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7687
                                    }  in
                                  (uu____7685, i)))
                       in
                    FStar_All.pipe_right uu____7625
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7711 =
                      let uu____7716 = FStar_Syntax_Subst.compress body  in
                      let uu____7717 =
                        let uu____7718 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7718
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7716 uu____7717
                       in
                    uu____7711 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___37_7769 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___37_7769.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___37_7769.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___37_7769.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___37_7769.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___37_7769.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___37_7769.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___37_7769.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___37_7769.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___37_7769.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___37_7769.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___37_7769.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___37_7769.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___37_7769.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___37_7769.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___37_7769.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___37_7769.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___37_7769.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___37_7769.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___37_7769.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___37_7769.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___37_7769.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___37_7769.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___37_7769.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___37_7769.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___37_7769.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___37_7769.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___37_7769.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___37_7769.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___37_7769.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___37_7769.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___37_7769.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___37_7769.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___37_7769.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___37_7769.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___37_7769.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___37_7769.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___37_7769.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___37_7769.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___37_7769.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___37_7769.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___37_7769.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___37_7769.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7841  ->
                       fun uu____7842  ->
                         match (uu____7841, uu____7842) with
                         | ((x,uu____7868),(b,uu____7870)) ->
                             let uu____7891 =
                               let uu____7898 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7898)  in
                             FStar_Syntax_Syntax.NT uu____7891) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7923 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7923
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7952 ->
                    let uu____7959 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7959
                | uu____7960 when Prims.op_Negation norm1 ->
                    let t_norm =
                      FStar_TypeChecker_Normalize.normalize
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
                | uu____7963 ->
                    let uu____7964 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7964)
                 in
              let aux t1 e1 =
                let uu____8006 = FStar_Syntax_Util.abs_formals e1  in
                match uu____8006 with
                | (binders,body,lopt) ->
                    let uu____8038 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____8054 -> arrow_formals_comp_norm false t1  in
                    (match uu____8038 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____8088 =
                           if nformals < nbinders
                           then
                             let uu____8132 =
                               FStar_Util.first_N nformals binders  in
                             match uu____8132 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____8216 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____8216)
                           else
                             if nformals > nbinders
                             then
                               (let uu____8256 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____8256 with
                                | (binders1,body1) ->
                                    let uu____8309 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____8309))
                             else
                               (let uu____8322 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____8322))
                            in
                         (match uu____8088 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____8382 = aux t e  in
              match uu____8382 with
              | (binders,body,comp) ->
                  let uu____8428 =
                    let uu____8439 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____8439
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____8454 = aux comp1 body1  in
                      match uu____8454 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____8428 with
                   | (binders1,body1,comp1) ->
                       let uu____8537 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____8537, comp1))
               in
            (try
               (fun uu___39_8564  ->
                  match () with
                  | () ->
                      let uu____8571 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8571
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8587 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8650  ->
                                   fun lb  ->
                                     match uu____8650 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8705 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8705
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8711 =
                                             let uu____8720 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8720
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8711 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8587 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____8861;
                                    FStar_Syntax_Syntax.lbeff = uu____8862;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8864;
                                    FStar_Syntax_Syntax.lbpos = uu____8865;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8889 =
                                     let uu____8896 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8896 with
                                     | (tcenv',uu____8912,e_t) ->
                                         let uu____8918 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8929 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8918 with
                                          | (e1,t_norm1) ->
                                              ((let uu___40_8946 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___40_8946.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8889 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8956 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____8956 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8976 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8976
                                               then
                                                 let uu____8981 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8984 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8981 uu____8984
                                               else ());
                                              (let uu____8989 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8989 with
                                               | (vars,_guards,env'1,binder_decls,uu____9016)
                                                   ->
                                                   let uu____9029 =
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
                                                         let uu____9046 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn
                                                            in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____9046
                                                          in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____9068 =
                                                          let uu____9069 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn
                                                             in
                                                          let uu____9070 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____9069 fvb
                                                            uu____9070
                                                           in
                                                        (vars, uu____9068))
                                                      in
                                                   (match uu____9029 with
                                                    | (vars1,app) ->
                                                        let uu____9081 =
                                                          let is_logical =
                                                            let uu____9094 =
                                                              let uu____9095
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body
                                                                 in
                                                              uu____9095.FStar_Syntax_Syntax.n
                                                               in
                                                            match uu____9094
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____9101 ->
                                                                false
                                                             in
                                                          let is_prims =
                                                            let uu____9105 =
                                                              let uu____9106
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9106
                                                                FStar_Syntax_Syntax.lid_of_fv
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____9105
                                                              (fun lid  ->
                                                                 let uu____9115
                                                                   =
                                                                   FStar_Ident.lid_of_ids
                                                                    lid.FStar_Ident.ns
                                                                    in
                                                                 FStar_Ident.lid_equals
                                                                   uu____9115
                                                                   FStar_Parser_Const.prims_lid)
                                                             in
                                                          let uu____9116 =
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
                                                          if uu____9116
                                                          then
                                                            let uu____9132 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app
                                                               in
                                                            let uu____9133 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1
                                                               in
                                                            (app, uu____9132,
                                                              uu____9133)
                                                          else
                                                            (let uu____9144 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1
                                                                in
                                                             (app, app,
                                                               uu____9144))
                                                           in
                                                        (match uu____9081
                                                         with
                                                         | (pat,app1,
                                                            (body1,decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____9168
                                                                 =
                                                                 let uu____9176
                                                                   =
                                                                   let uu____9177
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                   let uu____9178
                                                                    =
                                                                    let uu____9189
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                     in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____9189)
                                                                     in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____9177
                                                                    uu____9178
                                                                    in
                                                                 let uu____9198
                                                                   =
                                                                   let uu____9199
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9199
                                                                    in
                                                                 (uu____9176,
                                                                   uu____9198,
                                                                   (Prims.strcat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id))
                                                                  in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____9168
                                                                in
                                                             let uu____9205 =
                                                               let uu____9208
                                                                 =
                                                                 let uu____9211
                                                                   =
                                                                   let uu____9214
                                                                    =
                                                                    let uu____9217
                                                                    =
                                                                    let uu____9220
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                    eqn ::
                                                                    uu____9220
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____9217
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____9214
                                                                    in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____9211
                                                                  in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____9208
                                                                in
                                                             (uu____9205,
                                                               env2)))))))
                               | uu____9229 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9289 =
                                   let uu____9295 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel"
                                      in
                                   (uu____9295,
                                     FStar_SMTEncoding_Term.Fuel_sort)
                                    in
                                 FStar_SMTEncoding_Term.mk_fv uu____9289  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9301 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9354  ->
                                         fun fvb  ->
                                           match uu____9354 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9409 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9409
                                                  in
                                               let gtok =
                                                 let uu____9413 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9413
                                                  in
                                               let env4 =
                                                 let uu____9416 =
                                                   let uu____9419 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9419
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9416
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9301 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9544
                                     t_norm uu____9546 =
                                     match (uu____9544, uu____9546) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9576;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9577;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9579;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9580;_})
                                         ->
                                         let uu____9607 =
                                           let uu____9614 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9614 with
                                           | (tcenv',uu____9630,e_t) ->
                                               let uu____9636 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9647 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9636 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___41_9664 = env3
                                                         in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___41_9664.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9607 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9677 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9677
                                                then
                                                  let uu____9682 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9684 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9686 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9682 uu____9684
                                                    uu____9686
                                                else ());
                                               (let uu____9691 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____9691 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9718 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9718 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9740 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9740
                                                           then
                                                             let uu____9745 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9747 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9750 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9752 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9745
                                                               uu____9747
                                                               uu____9750
                                                               uu____9752
                                                           else ());
                                                          (let uu____9757 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9757
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9786)
                                                               ->
                                                               let uu____9799
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9812
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9812,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9816
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9816
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9829
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9829,
                                                                    decls0))
                                                                  in
                                                               (match uu____9799
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
                                                                    let uu____9850
                                                                    =
                                                                    let uu____9862
                                                                    =
                                                                    let uu____9865
                                                                    =
                                                                    let uu____9868
                                                                    =
                                                                    let uu____9871
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9871
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____9868
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9865
                                                                     in
                                                                    (g,
                                                                    uu____9862,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9850
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
                                                                    let uu____9901
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9901
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
                                                                    (Prims.parse_int "1"))
                                                                    args  in
                                                                    let gsapp
                                                                    =
                                                                    let uu____9916
                                                                    =
                                                                    let uu____9919
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9919
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9916
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9925
                                                                    =
                                                                    let uu____9928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9928
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9925
                                                                     in
                                                                    let uu____9933
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9933
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9949
                                                                    =
                                                                    let uu____9957
                                                                    =
                                                                    let uu____9958
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9959
                                                                    =
                                                                    let uu____9975
                                                                    =
                                                                    let uu____9976
                                                                    =
                                                                    let uu____9981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9981)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9976
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9975)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9958
                                                                    uu____9959
                                                                     in
                                                                    let uu____9995
                                                                    =
                                                                    let uu____9996
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9996
                                                                     in
                                                                    (uu____9957,
                                                                    uu____9995,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9949
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____10003
                                                                    =
                                                                    let uu____10011
                                                                    =
                                                                    let uu____10012
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10013
                                                                    =
                                                                    let uu____10024
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10024)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10012
                                                                    uu____10013
                                                                     in
                                                                    (uu____10011,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10003
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____10038
                                                                    =
                                                                    let uu____10046
                                                                    =
                                                                    let uu____10047
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10048
                                                                    =
                                                                    let uu____10059
                                                                    =
                                                                    let uu____10060
                                                                    =
                                                                    let uu____10065
                                                                    =
                                                                    let uu____10066
                                                                    =
                                                                    let uu____10069
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10069
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____10066
                                                                     in
                                                                    (gsapp,
                                                                    uu____10065)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10060
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10059)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10047
                                                                    uu____10048
                                                                     in
                                                                    (uu____10046,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10038
                                                                     in
                                                                    let uu____10083
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
                                                                    let uu____10095
                                                                    =
                                                                    let uu____10096
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____10096
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10095
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____10098
                                                                    =
                                                                    let uu____10106
                                                                    =
                                                                    let uu____10107
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10108
                                                                    =
                                                                    let uu____10119
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10119)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10107
                                                                    uu____10108
                                                                     in
                                                                    (uu____10106,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10098
                                                                     in
                                                                    let uu____10132
                                                                    =
                                                                    let uu____10141
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____10141
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10156
                                                                    =
                                                                    let uu____10159
                                                                    =
                                                                    let uu____10160
                                                                    =
                                                                    let uu____10168
                                                                    =
                                                                    let uu____10169
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10170
                                                                    =
                                                                    let uu____10181
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10181)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10169
                                                                    uu____10170
                                                                     in
                                                                    (uu____10168,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10160
                                                                     in
                                                                    [uu____10159]
                                                                     in
                                                                    (d3,
                                                                    uu____10156)
                                                                     in
                                                                    match uu____10132
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____10083
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____10238
                                                                    =
                                                                    let uu____10241
                                                                    =
                                                                    let uu____10244
                                                                    =
                                                                    let uu____10247
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____10247
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____10244
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____10241
                                                                     in
                                                                    let uu____10254
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____10238,
                                                                    uu____10254,
                                                                    env02))))))))))
                                      in
                                   let uu____10259 =
                                     let uu____10272 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10335  ->
                                          fun uu____10336  ->
                                            match (uu____10335, uu____10336)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10461 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10461 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10272
                                      in
                                   (match uu____10259 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10528 =
                                          let isDeclFun uu___23_10545 =
                                            match uu___23_10545 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10547 -> true
                                            | uu____10560 -> false  in
                                          let uu____10562 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10562
                                            (fun decls3  ->
                                               let uu____10592 =
                                                 FStar_List.fold_left
                                                   (fun uu____10623  ->
                                                      fun elt  ->
                                                        match uu____10623
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____10664 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____10664
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____10692
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____10692
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
                                                                    let uu___42_10730
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___42_10730.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___42_10730.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___42_10730.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____10592 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____10762 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____10762, elts, rest))
                                           in
                                        (match uu____10528 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____10791 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___24_10797  ->
                                        match uu___24_10797 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10800 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10808 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10808)))
                                in
                             if uu____10791
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___44_10830  ->
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
                   let uu____10869 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10869
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____10888 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____10888, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____10944 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10944 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10950 = encode_sigelt' env se  in
      match uu____10950 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10962 =
                  let uu____10965 =
                    let uu____10966 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____10966  in
                  [uu____10965]  in
                FStar_All.pipe_right uu____10962
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____10971 ->
                let uu____10972 =
                  let uu____10975 =
                    let uu____10978 =
                      let uu____10979 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____10979  in
                    [uu____10978]  in
                  FStar_All.pipe_right uu____10975
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____10986 =
                  let uu____10989 =
                    let uu____10992 =
                      let uu____10995 =
                        let uu____10996 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____10996  in
                      [uu____10995]  in
                    FStar_All.pipe_right uu____10992
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____10989  in
                FStar_List.append uu____10972 uu____10986
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      (let uu____11010 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____11010
       then
         let uu____11015 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____11015
       else ());
      (let is_opaque_to_smt t =
         let uu____11027 =
           let uu____11028 = FStar_Syntax_Subst.compress t  in
           uu____11028.FStar_Syntax_Syntax.n  in
         match uu____11027 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____11033)) -> s = "opaque_to_smt"
         | uu____11038 -> false  in
       let is_uninterpreted_by_smt t =
         let uu____11047 =
           let uu____11048 = FStar_Syntax_Subst.compress t  in
           uu____11048.FStar_Syntax_Syntax.n  in
         match uu____11047 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s,uu____11053)) -> s = "uninterpreted_by_smt"
         | uu____11058 -> false  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11064 ->
           failwith
             "impossible -- new_effect_for_free should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_splice uu____11070 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____11082 -> ([], env)
       | FStar_Syntax_Syntax.Sig_main uu____11083 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11084 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____11097 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____11099 =
             let uu____11101 =
               FStar_TypeChecker_Env.is_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
                in
             Prims.op_Negation uu____11101  in
           if uu____11099
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____11130 ->
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
                let uu____11162 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ
                   in
                match uu____11162 with
                | (formals,uu____11182) ->
                    let arity = FStar_List.length formals  in
                    let uu____11206 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity
                       in
                    (match uu____11206 with
                     | (aname,atok,env2) ->
                         let uu____11232 =
                           let uu____11237 =
                             close_effect_params
                               a.FStar_Syntax_Syntax.action_defn
                              in
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             uu____11237 env2
                            in
                         (match uu____11232 with
                          | (tm,decls) ->
                              let a_decls =
                                let uu____11249 =
                                  let uu____11250 =
                                    let uu____11262 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____11282  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, uu____11262,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action"))
                                     in
                                  FStar_SMTEncoding_Term.DeclFun uu____11250
                                   in
                                [uu____11249;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))]
                                 in
                              let uu____11299 =
                                let aux uu____11345 uu____11346 =
                                  match (uu____11345, uu____11346) with
                                  | ((bv,uu____11390),(env3,acc_sorts,acc))
                                      ->
                                      let uu____11422 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv
                                         in
                                      (match uu____11422 with
                                       | (xxsym,xx,env4) ->
                                           let uu____11445 =
                                             let uu____11448 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort)
                                                in
                                             uu____11448 :: acc_sorts  in
                                           (env4, uu____11445, (xx :: acc)))
                                   in
                                FStar_List.fold_right aux formals
                                  (env2, [], [])
                                 in
                              (match uu____11299 with
                               | (uu____11480,xs_sorts,xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs)
                                      in
                                   let a_eq =
                                     let uu____11496 =
                                       let uu____11504 =
                                         let uu____11505 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11506 =
                                           let uu____11517 =
                                             let uu____11518 =
                                               let uu____11523 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts
                                                  in
                                               (app, uu____11523)  in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____11518
                                              in
                                           ([[app]], xs_sorts, uu____11517)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11505 uu____11506
                                          in
                                       (uu____11504,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.strcat aname "_equality"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11496
                                      in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____11538 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                          in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____11538
                                        in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts
                                        in
                                     let uu____11541 =
                                       let uu____11549 =
                                         let uu____11550 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name
                                            in
                                         let uu____11551 =
                                           let uu____11562 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app)
                                              in
                                           ([[tok_app]], xs_sorts,
                                             uu____11562)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11550 uu____11551
                                          in
                                       (uu____11549,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.strcat aname
                                            "_token_correspondence"))
                                        in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11541
                                      in
                                   let uu____11575 =
                                     let uu____11578 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append decls uu____11578  in
                                   (env2, uu____11575))))
                 in
              let uu____11587 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions
                 in
              match uu____11587 with
              | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11613,uu____11614)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____11615 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.parse_int "4")
              in
           (match uu____11615 with | (tname,ttok,env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11637,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let will_encode_definition =
             let uu____11644 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___25_11650  ->
                       match uu___25_11650 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____11653 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11659 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____11662 -> false))
                in
             Prims.op_Negation uu____11644  in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              let uu____11672 =
                let uu____11677 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt)
                   in
                encode_top_level_val uu____11677 env fv t quals  in
              match uu____11672 with
              | (decls,env1) ->
                  let tname = lid.FStar_Ident.str  in
                  let tsym =
                    let uu____11691 =
                      FStar_SMTEncoding_Term.mk_fv
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____11691
                     in
                  let uu____11693 =
                    let uu____11694 =
                      let uu____11697 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym
                         in
                      FStar_All.pipe_right uu____11697
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    FStar_List.append decls uu____11694  in
                  (uu____11693, env1))
       | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
           let uu____11707 = FStar_Syntax_Subst.open_univ_vars us f  in
           (match uu____11707 with
            | (uvs,f1) ->
                let env1 =
                  let uu___45_11719 = env  in
                  let uu____11720 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs
                     in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___45_11719.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___45_11719.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___45_11719.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____11720;
                    FStar_SMTEncoding_Env.warn =
                      (uu___45_11719.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___45_11719.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___45_11719.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___45_11719.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___45_11719.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___45_11719.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___45_11719.FStar_SMTEncoding_Env.global_cache)
                  }  in
                let f2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Eager_unfolding]
                    env1.FStar_SMTEncoding_Env.tcenv f1
                   in
                let uu____11722 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
                (match uu____11722 with
                 | (f3,decls) ->
                     let g =
                       let uu____11736 =
                         let uu____11739 =
                           let uu____11740 =
                             let uu____11748 =
                               let uu____11749 =
                                 let uu____11751 =
                                   FStar_Syntax_Print.lid_to_string l  in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____11751
                                  in
                               FStar_Pervasives_Native.Some uu____11749  in
                             let uu____11755 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 (Prims.strcat "assumption_"
                                    l.FStar_Ident.str)
                                in
                             (f3, uu____11748, uu____11755)  in
                           FStar_SMTEncoding_Util.mkAssume uu____11740  in
                         [uu____11739]  in
                       FStar_All.pipe_right uu____11736
                         FStar_SMTEncoding_Term.mk_decls_trivial
                        in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____11764) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____11778 =
             FStar_Util.fold_map
               (fun env1  ->
                  fun lb  ->
                    let lid =
                      let uu____11800 =
                        let uu____11803 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        uu____11803.FStar_Syntax_Syntax.fv_name  in
                      uu____11800.FStar_Syntax_Syntax.v  in
                    let uu____11804 =
                      let uu____11806 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid
                         in
                      FStar_All.pipe_left FStar_Option.isNone uu____11806  in
                    if uu____11804
                    then
                      let val_decl =
                        let uu___46_11838 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___46_11838.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___46_11838.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___46_11838.FStar_Syntax_Syntax.sigattrs)
                        }  in
                      let uu____11839 = encode_sigelt' env1 val_decl  in
                      match uu____11839 with | (decls,env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
              in
           (match uu____11778 with
            | (env1,decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____11875,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                           FStar_Syntax_Syntax.lbunivs = uu____11877;
                           FStar_Syntax_Syntax.lbtyp = uu____11878;
                           FStar_Syntax_Syntax.lbeff = uu____11879;
                           FStar_Syntax_Syntax.lbdef = uu____11880;
                           FStar_Syntax_Syntax.lbattrs = uu____11881;
                           FStar_Syntax_Syntax.lbpos = uu____11882;_}::[]),uu____11883)
           when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
           ->
           let uu____11902 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               (Prims.parse_int "1")
              in
           (match uu____11902 with
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
                  let uu____11940 =
                    let uu____11943 =
                      let uu____11944 =
                        let uu____11952 =
                          let uu____11953 =
                            FStar_Syntax_Syntax.range_of_fv b2t1  in
                          let uu____11954 =
                            let uu____11965 =
                              let uu____11966 =
                                let uu____11971 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x])
                                   in
                                (valid_b2t_x, uu____11971)  in
                              FStar_SMTEncoding_Util.mkEq uu____11966  in
                            ([[b2t_x]], [xx], uu____11965)  in
                          FStar_SMTEncoding_Term.mkForall uu____11953
                            uu____11954
                           in
                        (uu____11952,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def")
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____11944  in
                    [uu____11943]  in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____11940
                   in
                let uu____12009 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                (uu____12009, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____12012,uu____12013) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___26_12023  ->
                   match uu___26_12023 with
                   | FStar_Syntax_Syntax.Discriminator uu____12025 -> true
                   | uu____12027 -> false))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let (uu____12029,lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l  ->
                    let uu____12041 =
                      let uu____12043 = FStar_List.hd l.FStar_Ident.ns  in
                      uu____12043.FStar_Ident.idText  in
                    uu____12041 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___27_12050  ->
                      match uu___27_12050 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                          -> true
                      | uu____12053 -> false)))
           -> ([], env)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12056) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___28_12070  ->
                   match uu___28_12070 with
                   | FStar_Syntax_Syntax.Projector uu____12072 -> true
                   | uu____12078 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
           let uu____12082 = FStar_SMTEncoding_Env.try_lookup_free_var env l
              in
           (match uu____12082 with
            | FStar_Pervasives_Native.Some uu____12089 -> ([], env)
            | FStar_Pervasives_Native.None  ->
                let se1 =
                  let uu___47_12091 = se  in
                  let uu____12092 = FStar_Ident.range_of_lid l  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____12092;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___47_12091.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___47_12091.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___47_12091.FStar_Syntax_Syntax.sigattrs)
                  }  in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12095) ->
           encode_top_level_let env (is_rec, bindings)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12110) ->
           let uu____12119 = encode_sigelts env ses  in
           (match uu____12119 with
            | (g,env1) ->
                let uu____12130 =
                  FStar_List.fold_left
                    (fun uu____12154  ->
                       fun elt  ->
                         match uu____12154 with
                         | (g',inversions) ->
                             let uu____12182 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___29_12205  ->
                                       match uu___29_12205 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____12207;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____12208;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____12209;_}
                                           -> false
                                       | uu____12216 -> true))
                                in
                             (match uu____12182 with
                              | (elt_g',elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___48_12241 = elt  in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___48_12241.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___48_12241.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___48_12241.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g
                   in
                (match uu____12130 with
                 | (g',inversions) ->
                     let uu____12260 =
                       FStar_List.fold_left
                         (fun uu____12291  ->
                            fun elt  ->
                              match uu____12291 with
                              | (decls,elts,rest) ->
                                  let uu____12332 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___30_12341  ->
                                            match uu___30_12341 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12343 -> true
                                            | uu____12356 -> false)
                                         elt.FStar_SMTEncoding_Term.decls)
                                     in
                                  if uu____12332
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____12379 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___31_12400  ->
                                               match uu___31_12400 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____12402 -> true
                                               | uu____12415 -> false))
                                        in
                                     match uu____12379 with
                                     | (elt_decls,elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___49_12446 = elt  in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___49_12446.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___49_12446.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___49_12446.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g'
                        in
                     (match uu____12260 with
                      | (decls,elts,rest) ->
                          let uu____12472 =
                            let uu____12473 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial
                               in
                            let uu____12480 =
                              let uu____12483 =
                                let uu____12486 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append rest uu____12486  in
                              FStar_List.append elts uu____12483  in
                            FStar_List.append uu____12473 uu____12480  in
                          (uu____12472, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t,uu____12494,tps,k,uu____12497,datas) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let is_logical =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___32_12516  ->
                     match uu___32_12516 with
                     | FStar_Syntax_Syntax.Logic  -> true
                     | FStar_Syntax_Syntax.Assumption  -> true
                     | uu____12520 -> false))
              in
           let constructor_or_logic_type_decl c =
             if is_logical
             then
               let uu____12533 = c  in
               match uu____12533 with
               | (name,args,uu____12538,uu____12539,uu____12540) ->
                   let uu____12551 =
                     let uu____12552 =
                       let uu____12564 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____12591  ->
                                 match uu____12591 with
                                 | (uu____12600,sort,uu____12602) -> sort))
                          in
                       (name, uu____12564, FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                        in
                     FStar_SMTEncoding_Term.DeclFun uu____12552  in
                   [uu____12551]
             else
               (let uu____12613 = FStar_Ident.range_of_lid t  in
                FStar_SMTEncoding_Term.constructor_to_decl uu____12613 c)
              in
           let inversion_axioms tapp vars =
             let uu____12631 =
               FStar_All.pipe_right datas
                 (FStar_Util.for_some
                    (fun l  ->
                       let uu____12639 =
                         FStar_TypeChecker_Env.try_lookup_lid
                           env.FStar_SMTEncoding_Env.tcenv l
                          in
                       FStar_All.pipe_right uu____12639 FStar_Option.isNone))
                in
             if uu____12631
             then []
             else
               (let uu____12674 =
                  FStar_SMTEncoding_Env.fresh_fvar
                    env.FStar_SMTEncoding_Env.current_module_name "x"
                    FStar_SMTEncoding_Term.Term_sort
                   in
                match uu____12674 with
                | (xxsym,xx) ->
                    let uu____12687 =
                      FStar_All.pipe_right datas
                        (FStar_List.fold_left
                           (fun uu____12726  ->
                              fun l  ->
                                match uu____12726 with
                                | (out,decls) ->
                                    let uu____12746 =
                                      FStar_TypeChecker_Env.lookup_datacon
                                        env.FStar_SMTEncoding_Env.tcenv l
                                       in
                                    (match uu____12746 with
                                     | (uu____12757,data_t) ->
                                         let uu____12759 =
                                           FStar_Syntax_Util.arrow_formals
                                             data_t
                                            in
                                         (match uu____12759 with
                                          | (args,res) ->
                                              let indices =
                                                let uu____12803 =
                                                  let uu____12804 =
                                                    FStar_Syntax_Subst.compress
                                                      res
                                                     in
                                                  uu____12804.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____12803 with
                                                | FStar_Syntax_Syntax.Tm_app
                                                    (uu____12807,indices) ->
                                                    indices
                                                | uu____12833 -> []  in
                                              let env1 =
                                                FStar_All.pipe_right args
                                                  (FStar_List.fold_left
                                                     (fun env1  ->
                                                        fun uu____12863  ->
                                                          match uu____12863
                                                          with
                                                          | (x,uu____12871)
                                                              ->
                                                              let uu____12876
                                                                =
                                                                let uu____12877
                                                                  =
                                                                  let uu____12885
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x  in
                                                                  (uu____12885,
                                                                    [xx])
                                                                   in
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  uu____12877
                                                                 in
                                                              FStar_SMTEncoding_Env.push_term_var
                                                                env1 x
                                                                uu____12876)
                                                     env)
                                                 in
                                              let uu____12890 =
                                                FStar_SMTEncoding_EncodeTerm.encode_args
                                                  indices env1
                                                 in
                                              (match uu____12890 with
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
                                                       let uu____12915 =
                                                         FStar_List.map2
                                                           (fun v1  ->
                                                              fun a  ->
                                                                let uu____12923
                                                                  =
                                                                  let uu____12928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                  (uu____12928,
                                                                    a)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____12923)
                                                           vars indices1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____12915
                                                         FStar_SMTEncoding_Util.mk_and_l
                                                        in
                                                     let uu____12931 =
                                                       let uu____12932 =
                                                         let uu____12937 =
                                                           let uu____12938 =
                                                             let uu____12943
                                                               =
                                                               FStar_SMTEncoding_Env.mk_data_tester
                                                                 env1 l xx
                                                                in
                                                             (uu____12943,
                                                               eqs)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____12938
                                                            in
                                                         (out, uu____12937)
                                                          in
                                                       FStar_SMTEncoding_Util.mkOr
                                                         uu____12932
                                                        in
                                                     (uu____12931,
                                                       (FStar_List.append
                                                          decls decls'))))))))
                           (FStar_SMTEncoding_Util.mkFalse, []))
                       in
                    (match uu____12687 with
                     | (data_ax,decls) ->
                         let uu____12956 =
                           FStar_SMTEncoding_Env.fresh_fvar
                             env.FStar_SMTEncoding_Env.current_module_name
                             "f" FStar_SMTEncoding_Term.Fuel_sort
                            in
                         (match uu____12956 with
                          | (ffsym,ff) ->
                              let fuel_guarded_inversion =
                                let xx_has_type_sfuel =
                                  if
                                    (FStar_List.length datas) >
                                      (Prims.parse_int "1")
                                  then
                                    let uu____12973 =
                                      FStar_SMTEncoding_Util.mkApp
                                        ("SFuel", [ff])
                                       in
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel
                                      uu____12973 xx tapp
                                  else
                                    FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                      xx tapp
                                   in
                                let uu____12980 =
                                  let uu____12988 =
                                    let uu____12989 =
                                      FStar_Ident.range_of_lid t  in
                                    let uu____12990 =
                                      let uu____13001 =
                                        let uu____13002 =
                                          FStar_SMTEncoding_Term.mk_fv
                                            (ffsym,
                                              FStar_SMTEncoding_Term.Fuel_sort)
                                           in
                                        let uu____13004 =
                                          let uu____13007 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             in
                                          uu____13007 :: vars  in
                                        FStar_SMTEncoding_Env.add_fuel
                                          uu____13002 uu____13004
                                         in
                                      let uu____13009 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (xx_has_type_sfuel, data_ax)
                                         in
                                      ([[xx_has_type_sfuel]], uu____13001,
                                        uu____13009)
                                       in
                                    FStar_SMTEncoding_Term.mkForall
                                      uu____12989 uu____12990
                                     in
                                  let uu____13018 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                      (Prims.strcat "fuel_guarded_inversion_"
                                         t.FStar_Ident.str)
                                     in
                                  (uu____12988,
                                    (FStar_Pervasives_Native.Some
                                       "inversion axiom"), uu____13018)
                                   in
                                FStar_SMTEncoding_Util.mkAssume uu____12980
                                 in
                              let uu____13024 =
                                FStar_All.pipe_right [fuel_guarded_inversion]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              FStar_List.append decls uu____13024)))
              in
           let uu____13031 =
             let uu____13036 =
               let uu____13037 = FStar_Syntax_Subst.compress k  in
               uu____13037.FStar_Syntax_Syntax.n  in
             match uu____13036 with
             | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                 ((FStar_List.append tps formals),
                   (FStar_Syntax_Util.comp_result kres))
             | uu____13072 -> (tps, k)  in
           (match uu____13031 with
            | (formals,res) ->
                let uu____13079 = FStar_Syntax_Subst.open_term formals res
                   in
                (match uu____13079 with
                 | (formals1,res1) ->
                     let uu____13090 =
                       FStar_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals1 env
                        in
                     (match uu____13090 with
                      | (vars,guards,env',binder_decls,uu____13115) ->
                          let arity = FStar_List.length vars  in
                          let uu____13129 =
                            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env t arity
                             in
                          (match uu____13129 with
                           | (tname,ttok,env1) ->
                               let ttok_tm =
                                 FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards  in
                               let tapp =
                                 let uu____13159 =
                                   let uu____13167 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, uu____13167)  in
                                 FStar_SMTEncoding_Util.mkApp uu____13159  in
                               let uu____13173 =
                                 let tname_decl =
                                   let uu____13183 =
                                     let uu____13184 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun fv  ->
                                               let uu____13203 =
                                                 let uu____13205 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     fv
                                                    in
                                                 Prims.strcat tname
                                                   uu____13205
                                                  in
                                               let uu____13207 =
                                                 FStar_SMTEncoding_Term.fv_sort
                                                   fv
                                                  in
                                               (uu____13203, uu____13207,
                                                 false)))
                                        in
                                     let uu____13211 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         ()
                                        in
                                     (tname, uu____13184,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       uu____13211, false)
                                      in
                                   constructor_or_logic_type_decl uu____13183
                                    in
                                 let uu____13219 =
                                   match vars with
                                   | [] ->
                                       let uu____13232 =
                                         let uu____13233 =
                                           let uu____13236 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tname, [])
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_3  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_3) uu____13236
                                            in
                                         FStar_SMTEncoding_Env.push_free_var
                                           env1 t arity tname uu____13233
                                          in
                                       ([], uu____13232)
                                   | uu____13248 ->
                                       let ttok_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (ttok, [],
                                             FStar_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token"))
                                          in
                                       let ttok_fresh =
                                         let uu____13258 =
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                             ()
                                            in
                                         FStar_SMTEncoding_Term.fresh_token
                                           (ttok,
                                             FStar_SMTEncoding_Term.Term_sort)
                                           uu____13258
                                          in
                                       let ttok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars
                                          in
                                       let pats = [[ttok_app]; [tapp]]  in
                                       let name_tok_corr =
                                         let uu____13274 =
                                           let uu____13282 =
                                             let uu____13283 =
                                               FStar_Ident.range_of_lid t  in
                                             let uu____13284 =
                                               let uu____13300 =
                                                 FStar_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp)
                                                  in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 vars, uu____13300)
                                                in
                                             FStar_SMTEncoding_Term.mkForall'
                                               uu____13283 uu____13284
                                              in
                                           (uu____13282,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.strcat
                                                "token_correspondence_" ttok))
                                            in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____13274
                                          in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env1)
                                    in
                                 match uu____13219 with
                                 | (tok_decls,env2) ->
                                     let uu____13327 =
                                       FStar_Ident.lid_equals t
                                         FStar_Parser_Const.lex_t_lid
                                        in
                                     if uu____13327
                                     then (tok_decls, env2)
                                     else
                                       ((FStar_List.append tname_decl
                                           tok_decls), env2)
                                  in
                               (match uu____13173 with
                                | (decls,env2) ->
                                    let kindingAx =
                                      let uu____13355 =
                                        FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res1
                                          env' tapp
                                         in
                                      match uu____13355 with
                                      | (k1,decls1) ->
                                          let karr =
                                            if
                                              (FStar_List.length formals1) >
                                                (Prims.parse_int "0")
                                            then
                                              let uu____13377 =
                                                let uu____13378 =
                                                  let uu____13386 =
                                                    let uu____13387 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____13387
                                                     in
                                                  (uu____13386,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.strcat
                                                       "pre_kinding_" ttok))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____13378
                                                 in
                                              [uu____13377]
                                            else []  in
                                          let uu____13395 =
                                            let uu____13398 =
                                              let uu____13401 =
                                                let uu____13404 =
                                                  let uu____13405 =
                                                    let uu____13413 =
                                                      let uu____13414 =
                                                        FStar_Ident.range_of_lid
                                                          t
                                                         in
                                                      let uu____13415 =
                                                        let uu____13426 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1)
                                                           in
                                                        ([[tapp]], vars,
                                                          uu____13426)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____13414
                                                        uu____13415
                                                       in
                                                    (uu____13413,
                                                      FStar_Pervasives_Native.None,
                                                      (Prims.strcat
                                                         "kinding_" ttok))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____13405
                                                   in
                                                [uu____13404]  in
                                              FStar_List.append karr
                                                uu____13401
                                               in
                                            FStar_All.pipe_right uu____13398
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          FStar_List.append decls1
                                            uu____13395
                                       in
                                    let aux =
                                      let uu____13445 =
                                        let uu____13448 =
                                          inversion_axioms tapp vars  in
                                        let uu____13451 =
                                          let uu____13454 =
                                            let uu____13457 =
                                              let uu____13458 =
                                                FStar_Ident.range_of_lid t
                                                 in
                                              pretype_axiom uu____13458 env2
                                                tapp vars
                                               in
                                            [uu____13457]  in
                                          FStar_All.pipe_right uu____13454
                                            FStar_SMTEncoding_Term.mk_decls_trivial
                                           in
                                        FStar_List.append uu____13448
                                          uu____13451
                                         in
                                      FStar_List.append kindingAx uu____13445
                                       in
                                    let g =
                                      let uu____13466 =
                                        FStar_All.pipe_right decls
                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                         in
                                      FStar_List.append uu____13466
                                        (FStar_List.append binder_decls aux)
                                       in
                                    (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____13474,uu____13475,uu____13476,uu____13477,uu____13478)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d,uu____13486,t,uu____13488,n_tps,uu____13490) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____13500 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____13500 with
            | (formals,t_res) ->
                let arity = FStar_List.length formals  in
                let uu____13548 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity
                   in
                (match uu____13548 with
                 | (ddconstrsym,ddtok,env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                        in
                     let uu____13576 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort
                        in
                     (match uu____13576 with
                      | (fuel_var,fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                             in
                          let uu____13596 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1
                             in
                          (match uu____13596 with
                           | (vars,guards,env',binder_decls,names1) ->
                               let fields =
                                 FStar_All.pipe_right names1
                                   (FStar_List.mapi
                                      (fun n1  ->
                                         fun x  ->
                                           let projectible = true  in
                                           let uu____13675 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x
                                              in
                                           (uu____13675,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible)))
                                  in
                               let datacons =
                                 let uu____13682 =
                                   let uu____13683 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       ()
                                      in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____13683, true)
                                    in
                                 let uu____13691 =
                                   let uu____13698 =
                                     FStar_Ident.range_of_lid d  in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____13698
                                    in
                                 FStar_All.pipe_right uu____13682 uu____13691
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
                               let uu____13710 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t env1
                                   ddtok_tm
                                  in
                               (match uu____13710 with
                                | (tok_typing,decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____13722::uu____13723 ->
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
                                            let uu____13772 =
                                              let uu____13773 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              [uu____13773]  in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____13772
                                             in
                                          let uu____13799 =
                                            FStar_Ident.range_of_lid d  in
                                          let uu____13800 =
                                            let uu____13811 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing
                                               in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____13811)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____13799 uu____13800
                                      | uu____13838 -> tok_typing  in
                                    let uu____13849 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1
                                       in
                                    (match uu____13849 with
                                     | (vars',guards',env'',decls_formals,uu____13874)
                                         ->
                                         let uu____13887 =
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
                                         (match uu____13887 with
                                          | (ty_pred',decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards'
                                                 in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____13917 ->
                                                    let uu____13926 =
                                                      let uu____13927 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          ()
                                                         in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____13927
                                                       in
                                                    [uu____13926]
                                                 in
                                              let encode_elim uu____13943 =
                                                let uu____13944 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res
                                                   in
                                                match uu____13944 with
                                                | (head1,args) ->
                                                    let uu____13995 =
                                                      let uu____13996 =
                                                        FStar_Syntax_Subst.compress
                                                          head1
                                                         in
                                                      uu____13996.FStar_Syntax_Syntax.n
                                                       in
                                                    (match uu____13995 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____14008;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____14009;_},uu____14010)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name
                                                            in
                                                         let uu____14016 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____14016
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
                                                                  | uu____14079
                                                                    ->
                                                                    let uu____14080
                                                                    =
                                                                    let uu____14086
                                                                    =
                                                                    let uu____14088
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14088
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14086)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14080
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14111
                                                                    =
                                                                    let uu____14113
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14113
                                                                     in
                                                                    if
                                                                    uu____14111
                                                                    then
                                                                    let uu____14135
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14135]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14138
                                                                =
                                                                let uu____14152
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14209
                                                                     ->
                                                                    fun
                                                                    uu____14210
                                                                     ->
                                                                    match 
                                                                    (uu____14209,
                                                                    uu____14210)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14321
                                                                    =
                                                                    let uu____14329
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14329
                                                                     in
                                                                    (match uu____14321
                                                                    with
                                                                    | 
                                                                    (uu____14343,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14354
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14354
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14359
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14359
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____14152
                                                                 in
                                                              (match uu____14138
                                                               with
                                                               | (uu____14380,arg_vars,elim_eqns_or_guards,uu____14383)
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
                                                                    let uu____14410
                                                                    =
                                                                    let uu____14418
                                                                    =
                                                                    let uu____14419
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14420
                                                                    =
                                                                    let uu____14431
                                                                    =
                                                                    let uu____14432
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14432
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14434
                                                                    =
                                                                    let uu____14435
                                                                    =
                                                                    let uu____14440
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14440)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14435
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14431,
                                                                    uu____14434)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14419
                                                                    uu____14420
                                                                     in
                                                                    (uu____14418,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14410
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14455
                                                                    =
                                                                    let uu____14456
                                                                    =
                                                                    let uu____14462
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14462,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14456
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14455
                                                                     in
                                                                    let uu____14465
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14465
                                                                    then
                                                                    let x =
                                                                    let uu____14469
                                                                    =
                                                                    let uu____14475
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____14475,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14469
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14480
                                                                    =
                                                                    let uu____14488
                                                                    =
                                                                    let uu____14489
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14490
                                                                    =
                                                                    let uu____14501
                                                                    =
                                                                    let uu____14506
                                                                    =
                                                                    let uu____14509
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14509]
                                                                     in
                                                                    [uu____14506]
                                                                     in
                                                                    let uu____14514
                                                                    =
                                                                    let uu____14515
                                                                    =
                                                                    let uu____14520
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14522
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14520,
                                                                    uu____14522)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14515
                                                                     in
                                                                    (uu____14501,
                                                                    [x],
                                                                    uu____14514)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14489
                                                                    uu____14490
                                                                     in
                                                                    let uu____14543
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14488,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14543)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14480
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14554
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
                                                                    (let uu____14577
                                                                    =
                                                                    let uu____14578
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14578
                                                                    dapp1  in
                                                                    [uu____14577])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14554
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14593
                                                                    =
                                                                    let uu____14594
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14595
                                                                    =
                                                                    let uu____14606
                                                                    =
                                                                    let uu____14607
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14607
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14609
                                                                    =
                                                                    let uu____14610
                                                                    =
                                                                    let uu____14615
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14615)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14610
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14606,
                                                                    uu____14609)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14594
                                                                    uu____14595
                                                                     in
                                                                    (uu____14593,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14585)
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
                                                         let uu____14634 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env'
                                                            in
                                                         (match uu____14634
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
                                                                  | uu____14697
                                                                    ->
                                                                    let uu____14698
                                                                    =
                                                                    let uu____14704
                                                                    =
                                                                    let uu____14706
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14706
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14704)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14698
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14729
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14731
                                                                     in
                                                                    if
                                                                    uu____14729
                                                                    then
                                                                    let uu____14753
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14753]
                                                                    else []))
                                                                   in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1
                                                                 in
                                                              let uu____14756
                                                                =
                                                                let uu____14770
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                   in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14827
                                                                     ->
                                                                    fun
                                                                    uu____14828
                                                                     ->
                                                                    match 
                                                                    (uu____14827,
                                                                    uu____14828)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14939
                                                                    =
                                                                    let uu____14947
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14947
                                                                     in
                                                                    (match uu____14939
                                                                    with
                                                                    | 
                                                                    (uu____14961,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14972
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14972
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14977
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14977
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                  (env', [],
                                                                    [],
                                                                    (Prims.parse_int "0"))
                                                                  uu____14770
                                                                 in
                                                              (match uu____14756
                                                               with
                                                               | (uu____14998,arg_vars,elim_eqns_or_guards,uu____15001)
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
                                                                    let uu____15028
                                                                    =
                                                                    let uu____15036
                                                                    =
                                                                    let uu____15037
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15038
                                                                    =
                                                                    let uu____15049
                                                                    =
                                                                    let uu____15050
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15050
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15052
                                                                    =
                                                                    let uu____15053
                                                                    =
                                                                    let uu____15058
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15058)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15053
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15049,
                                                                    uu____15052)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15037
                                                                    uu____15038
                                                                     in
                                                                    (uu____15036,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15028
                                                                     in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15073
                                                                    =
                                                                    let uu____15074
                                                                    =
                                                                    let uu____15080
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15080,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15074
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15073
                                                                     in
                                                                    let uu____15083
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15083
                                                                    then
                                                                    let x =
                                                                    let uu____15087
                                                                    =
                                                                    let uu____15093
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    env1.FStar_SMTEncoding_Env.current_module_name
                                                                    "x"  in
                                                                    (uu____15093,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15087
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15098
                                                                    =
                                                                    let uu____15106
                                                                    =
                                                                    let uu____15107
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15108
                                                                    =
                                                                    let uu____15119
                                                                    =
                                                                    let uu____15124
                                                                    =
                                                                    let uu____15127
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15127]
                                                                     in
                                                                    [uu____15124]
                                                                     in
                                                                    let uu____15132
                                                                    =
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15138
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15140
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15138,
                                                                    uu____15140)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15133
                                                                     in
                                                                    (uu____15119,
                                                                    [x],
                                                                    uu____15132)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15107
                                                                    uu____15108
                                                                     in
                                                                    let uu____15161
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15106,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15161)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15098
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15172
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
                                                                    (let uu____15195
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15196
                                                                    dapp1  in
                                                                    [uu____15195])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15172
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15203
                                                                    =
                                                                    let uu____15211
                                                                    =
                                                                    let uu____15212
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15213
                                                                    =
                                                                    let uu____15224
                                                                    =
                                                                    let uu____15225
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15225
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15227
                                                                    =
                                                                    let uu____15228
                                                                    =
                                                                    let uu____15233
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15233)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15228
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15224,
                                                                    uu____15227)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15212
                                                                    uu____15213
                                                                     in
                                                                    (uu____15211,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15203)
                                                                     in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____15250 ->
                                                         ((let uu____15252 =
                                                             let uu____15258
                                                               =
                                                               let uu____15260
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d
                                                                  in
                                                               let uu____15262
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head1
                                                                  in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____15260
                                                                 uu____15262
                                                                in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____15258)
                                                              in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____15252);
                                                          ([], [])))
                                                 in
                                              let uu____15270 =
                                                encode_elim ()  in
                                              (match uu____15270 with
                                               | (decls2,elim) ->
                                                   let g =
                                                     let uu____15296 =
                                                       let uu____15299 =
                                                         let uu____15302 =
                                                           let uu____15305 =
                                                             let uu____15308
                                                               =
                                                               let uu____15311
                                                                 =
                                                                 let uu____15314
                                                                   =
                                                                   let uu____15315
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    let uu____15328
                                                                    =
                                                                    let uu____15330
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15330
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____15328
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____15327)
                                                                     in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____15315
                                                                    in
                                                                 [uu____15314]
                                                                  in
                                                               FStar_List.append
                                                                 uu____15311
                                                                 proxy_fresh
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15308
                                                               FStar_SMTEncoding_Term.mk_decls_trivial
                                                              in
                                                           let uu____15341 =
                                                             let uu____15344
                                                               =
                                                               let uu____15347
                                                                 =
                                                                 let uu____15350
                                                                   =
                                                                   let uu____15353
                                                                    =
                                                                    let uu____15356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15361
                                                                    =
                                                                    let uu____15364
                                                                    =
                                                                    let uu____15365
                                                                    =
                                                                    let uu____15373
                                                                    =
                                                                    let uu____15374
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15375
                                                                    =
                                                                    let uu____15386
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15386)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15374
                                                                    uu____15375
                                                                     in
                                                                    (uu____15373,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15365
                                                                     in
                                                                    let uu____15399
                                                                    =
                                                                    let uu____15402
                                                                    =
                                                                    let uu____15403
                                                                    =
                                                                    let uu____15411
                                                                    =
                                                                    let uu____15412
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15413
                                                                    =
                                                                    let uu____15424
                                                                    =
                                                                    let uu____15425
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15425
                                                                    vars'  in
                                                                    let uu____15427
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15424,
                                                                    uu____15427)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15412
                                                                    uu____15413
                                                                     in
                                                                    (uu____15411,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15403
                                                                     in
                                                                    [uu____15402]
                                                                     in
                                                                    uu____15364
                                                                    ::
                                                                    uu____15399
                                                                     in
                                                                    uu____15356
                                                                    ::
                                                                    uu____15361
                                                                     in
                                                                   FStar_List.append
                                                                    uu____15353
                                                                    elim
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____15350
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                                                  in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____15347
                                                                in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____15344
                                                              in
                                                           FStar_List.append
                                                             uu____15305
                                                             uu____15341
                                                            in
                                                         FStar_List.append
                                                           decls3 uu____15302
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____15299
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____15296
                                                      in
                                                   let uu____15444 =
                                                     let uu____15445 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       uu____15445 g
                                                      in
                                                   (uu____15444, env1))))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15479  ->
              fun se  ->
                match uu____15479 with
                | (g,env1) ->
                    let uu____15499 = encode_sigelt env1 se  in
                    (match uu____15499 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15567 =
        match uu____15567 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15604 ->
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
                 ((let uu____15612 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15612
                   then
                     let uu____15617 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15619 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15621 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15617 uu____15619 uu____15621
                   else ());
                  (let uu____15626 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15626 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15644 =
                         let uu____15652 =
                           let uu____15654 =
                             let uu____15656 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15656
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15654  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15652
                          in
                       (match uu____15644 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15676 = FStar_Options.log_queries ()
                                 in
                              if uu____15676
                              then
                                let uu____15679 =
                                  let uu____15681 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15683 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15685 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15681 uu____15683 uu____15685
                                   in
                                FStar_Pervasives_Native.Some uu____15679
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____15701 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____15711 =
                                let uu____15714 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____15714  in
                              FStar_List.append uu____15701 uu____15711  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15726,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15746 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15746 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15767 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15767 with | (uu____15794,decls,env1) -> (decls, env1)
  
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15847  ->
              match uu____15847 with
              | (l,uu____15856,uu____15857) ->
                  let uu____15860 =
                    let uu____15872 = FStar_SMTEncoding_Term.fv_name l  in
                    (uu____15872, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)
                     in
                  FStar_SMTEncoding_Term.DeclFun uu____15860))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15905  ->
              match uu____15905 with
              | (l,uu____15916,uu____15917) ->
                  let uu____15920 =
                    let uu____15921 = FStar_SMTEncoding_Term.fv_name l  in
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      uu____15921
                     in
                  let uu____15924 =
                    let uu____15927 =
                      let uu____15928 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15928  in
                    [uu____15927]  in
                  uu____15920 :: uu____15924))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15957 =
      let uu____15960 =
        let uu____15961 = FStar_Util.psmap_empty ()  in
        let uu____15976 =
          let uu____15985 = FStar_Util.psmap_empty ()  in (uu____15985, [])
           in
        let uu____15992 =
          let uu____15994 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15994 FStar_Ident.string_of_lid  in
        let uu____15996 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15961;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15976;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15992;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____15996
        }  in
      [uu____15960]  in
    FStar_ST.op_Colon_Equals last_env uu____15957
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16040 = FStar_ST.op_Bang last_env  in
      match uu____16040 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16068 ->
          let uu___50_16071 = e  in
          let uu____16072 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___50_16071.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___50_16071.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___50_16071.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___50_16071.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___50_16071.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___50_16071.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___50_16071.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16072;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___50_16071.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___50_16071.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16080 = FStar_ST.op_Bang last_env  in
    match uu____16080 with
    | [] -> failwith "Empty env stack"
    | uu____16107::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16139  ->
    let uu____16140 = FStar_ST.op_Bang last_env  in
    match uu____16140 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16200  ->
    let uu____16201 = FStar_ST.op_Bang last_env  in
    match uu____16201 with
    | [] -> failwith "Popping an empty stack"
    | uu____16228::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16265  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16318  ->
         let uu____16319 = snapshot_env ()  in
         match uu____16319 with
         | (env_depth,()) ->
             let uu____16341 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16341 with
              | (varops_depth,()) ->
                  let uu____16363 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16363 with
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
        (fun uu____16421  ->
           let uu____16422 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16422 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16517 = snapshot msg  in () 
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
        | (uu____16563::uu____16564,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___51_16572 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___51_16572.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___51_16572.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___51_16572.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16573 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___52_16600 = elt  in
        let uu____16601 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___52_16600.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___52_16600.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____16601;
          FStar_SMTEncoding_Term.a_names =
            (uu___52_16600.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16621 =
        let uu____16624 =
          let uu____16625 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16625  in
        let uu____16626 = open_fact_db_tags env  in uu____16624 ::
          uu____16626
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16621
  
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
      let uu____16653 = encode_sigelt env se  in
      match uu____16653 with
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
                (let uu____16699 =
                   let uu____16702 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____16702
                    in
                 match uu____16699 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____16717 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____16717
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____16747 = FStar_Options.log_queries ()  in
        if uu____16747
        then
          let uu____16752 =
            let uu____16753 =
              let uu____16755 =
                let uu____16757 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16757 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16755  in
            FStar_SMTEncoding_Term.Caption uu____16753  in
          uu____16752 :: decls
        else decls  in
      (let uu____16776 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____16776
       then
         let uu____16779 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16779
       else ());
      (let env =
         let uu____16785 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16785 tcenv  in
       let uu____16786 = encode_top_level_facts env se  in
       match uu____16786 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16800 =
               let uu____16803 =
                 let uu____16806 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____16806
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____16803  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16800)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____16839 = FStar_Options.log_queries ()  in
          if uu____16839
          then
            let msg = Prims.strcat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___53_16859 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___53_16859.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___53_16859.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___53_16859.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___53_16859.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___53_16859.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___53_16859.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___53_16859.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___53_16859.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___53_16859.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___53_16859.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____16864 =
             let uu____16867 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____16867
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____16864  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____16887 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16887
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
          (let uu____16911 =
             FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
           if uu____16911
           then
             let uu____16914 =
               FStar_All.pipe_right
                 (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                 Prims.string_of_int
                in
             FStar_Util.print2
               "+++++++++++Encoding externals for %s ... %s exports\n" name
               uu____16914
           else ());
          (let env =
             let uu____16922 = get_env modul.FStar_Syntax_Syntax.name tcenv
                in
             FStar_All.pipe_right uu____16922
               FStar_SMTEncoding_Env.reset_current_module_fvbs
              in
           let encode_signature env1 ses =
             FStar_All.pipe_right ses
               (FStar_List.fold_left
                  (fun uu____16961  ->
                     fun se  ->
                       match uu____16961 with
                       | (g,env2) ->
                           let uu____16981 = encode_top_level_facts env2 se
                              in
                           (match uu____16981 with
                            | (g',env3) -> ((FStar_List.append g g'), env3)))
                  ([], env1))
              in
           let uu____17004 =
             encode_signature
               (let uu___54_17013 = env  in
                {
                  FStar_SMTEncoding_Env.bvar_bindings =
                    (uu___54_17013.FStar_SMTEncoding_Env.bvar_bindings);
                  FStar_SMTEncoding_Env.fvar_bindings =
                    (uu___54_17013.FStar_SMTEncoding_Env.fvar_bindings);
                  FStar_SMTEncoding_Env.depth =
                    (uu___54_17013.FStar_SMTEncoding_Env.depth);
                  FStar_SMTEncoding_Env.tcenv =
                    (uu___54_17013.FStar_SMTEncoding_Env.tcenv);
                  FStar_SMTEncoding_Env.warn = false;
                  FStar_SMTEncoding_Env.nolabels =
                    (uu___54_17013.FStar_SMTEncoding_Env.nolabels);
                  FStar_SMTEncoding_Env.use_zfuel_name =
                    (uu___54_17013.FStar_SMTEncoding_Env.use_zfuel_name);
                  FStar_SMTEncoding_Env.encode_non_total_function_typ =
                    (uu___54_17013.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                  FStar_SMTEncoding_Env.current_module_name =
                    (uu___54_17013.FStar_SMTEncoding_Env.current_module_name);
                  FStar_SMTEncoding_Env.encoding_quantifier =
                    (uu___54_17013.FStar_SMTEncoding_Env.encoding_quantifier);
                  FStar_SMTEncoding_Env.global_cache =
                    (uu___54_17013.FStar_SMTEncoding_Env.global_cache)
                }) modul.FStar_Syntax_Syntax.exports
              in
           match uu____17004 with
           | (decls,env1) ->
               (give_decls_to_z3_and_set_env env1 name decls;
                (let uu____17029 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____17029
                 then
                   FStar_Util.print1 "Done encoding externals for %s\n" name
                 else ());
                (let uu____17035 =
                   FStar_All.pipe_right env1
                     FStar_SMTEncoding_Env.get_current_module_fvbs
                    in
                 (decls, uu____17035))))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____17063  ->
        match uu____17063 with
        | (decls,fvbs) ->
            ((let uu____17077 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____17077
              then ()
              else
                (let uu____17082 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____17082
                 then
                   let uu____17085 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____17085
                 else ()));
             (let env =
                let uu____17093 = get_env name tcenv  in
                FStar_All.pipe_right uu____17093
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____17095 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____17095
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____17109 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____17109
               then
                 FStar_Util.print1
                   "Done encoding externals from cache for %s\n"
                   name.FStar_Ident.str
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
        (let uu____17171 =
           let uu____17173 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17173.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17171);
        (let env =
           let uu____17175 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17175 tcenv  in
         let uu____17176 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17215 = aux rest  in
                 (match uu____17215 with
                  | (out,rest1) ->
                      let t =
                        let uu____17243 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17243 with
                        | FStar_Pervasives_Native.Some uu____17246 ->
                            let uu____17247 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17247
                              x.FStar_Syntax_Syntax.sort
                        | uu____17248 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17252 =
                        let uu____17255 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___55_17258 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___55_17258.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___55_17258.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17255 :: out  in
                      (uu____17252, rest1))
             | uu____17263 -> ([], bindings)  in
           let uu____17270 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17270 with
           | (closing,bindings) ->
               let uu____17297 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17297, bindings)
            in
         match uu____17176 with
         | (q1,bindings) ->
             let uu____17328 = encode_env_bindings env bindings  in
             (match uu____17328 with
              | (env_decls,env1) ->
                  ((let uu____17350 =
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
                    if uu____17350
                    then
                      let uu____17357 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17357
                    else ());
                   (let uu____17362 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17362 with
                    | (phi,qdecls) ->
                        let uu____17383 =
                          let uu____17388 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17388 phi
                           in
                        (match uu____17383 with
                         | (labels,phi1) ->
                             let uu____17405 = encode_labels labels  in
                             (match uu____17405 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17441 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17441
                                    then
                                      let uu____17446 =
                                        let uu____17447 =
                                          let uu____17449 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17449
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17447
                                         in
                                      [uu____17446]
                                    else []  in
                                  let query_prelude =
                                    let uu____17457 =
                                      let uu____17458 =
                                        let uu____17459 =
                                          let uu____17462 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____17469 =
                                            let uu____17472 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____17472
                                             in
                                          FStar_List.append uu____17462
                                            uu____17469
                                           in
                                        FStar_List.append env_decls
                                          uu____17459
                                         in
                                      FStar_All.pipe_right uu____17458
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____17457
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____17482 =
                                      let uu____17490 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17491 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17490,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17491)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17482
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
  