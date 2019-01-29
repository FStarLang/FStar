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
  let uu____136 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____136 with
  | (asym,a) ->
      let uu____147 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____147 with
       | (xsym,x) ->
           let uu____158 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____158 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____230 =
                      let uu____242 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____242, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____230  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____273 =
                      let uu____281 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____281)  in
                    FStar_SMTEncoding_Util.mkApp uu____273  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____297 =
                    let uu____300 =
                      let uu____303 =
                        let uu____306 =
                          let uu____307 =
                            let uu____315 =
                              let uu____316 =
                                let uu____327 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____327)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____316
                               in
                            (uu____315, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____307  in
                        let uu____339 =
                          let uu____342 =
                            let uu____343 =
                              let uu____351 =
                                let uu____352 =
                                  let uu____363 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____363)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____352
                                 in
                              (uu____351,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____343  in
                          [uu____342]  in
                        uu____306 :: uu____339  in
                      xtok_decl :: uu____303  in
                    xname_decl :: uu____300  in
                  (xtok1, (FStar_List.length vars), uu____297)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____482 =
                    let uu____503 =
                      let uu____522 =
                        let uu____523 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____523
                         in
                      quant axy uu____522  in
                    (FStar_Parser_Const.op_Eq, uu____503)  in
                  let uu____540 =
                    let uu____563 =
                      let uu____584 =
                        let uu____603 =
                          let uu____604 =
                            let uu____605 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____605  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____604
                           in
                        quant axy uu____603  in
                      (FStar_Parser_Const.op_notEq, uu____584)  in
                    let uu____622 =
                      let uu____645 =
                        let uu____666 =
                          let uu____685 =
                            let uu____686 =
                              let uu____687 =
                                let uu____692 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____693 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____692, uu____693)  in
                              FStar_SMTEncoding_Util.mkLT uu____687  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____686
                             in
                          quant xy uu____685  in
                        (FStar_Parser_Const.op_LT, uu____666)  in
                      let uu____710 =
                        let uu____733 =
                          let uu____754 =
                            let uu____773 =
                              let uu____774 =
                                let uu____775 =
                                  let uu____780 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____781 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____780, uu____781)  in
                                FStar_SMTEncoding_Util.mkLTE uu____775  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____774
                               in
                            quant xy uu____773  in
                          (FStar_Parser_Const.op_LTE, uu____754)  in
                        let uu____798 =
                          let uu____821 =
                            let uu____842 =
                              let uu____861 =
                                let uu____862 =
                                  let uu____863 =
                                    let uu____868 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____869 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____868, uu____869)  in
                                  FStar_SMTEncoding_Util.mkGT uu____863  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____862
                                 in
                              quant xy uu____861  in
                            (FStar_Parser_Const.op_GT, uu____842)  in
                          let uu____886 =
                            let uu____909 =
                              let uu____930 =
                                let uu____949 =
                                  let uu____950 =
                                    let uu____951 =
                                      let uu____956 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____957 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____956, uu____957)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____951
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____950
                                   in
                                quant xy uu____949  in
                              (FStar_Parser_Const.op_GTE, uu____930)  in
                            let uu____974 =
                              let uu____997 =
                                let uu____1018 =
                                  let uu____1037 =
                                    let uu____1038 =
                                      let uu____1039 =
                                        let uu____1044 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1045 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1044, uu____1045)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1039
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1038
                                     in
                                  quant xy uu____1037  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1018)
                                 in
                              let uu____1062 =
                                let uu____1085 =
                                  let uu____1106 =
                                    let uu____1125 =
                                      let uu____1126 =
                                        let uu____1127 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1127
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1126
                                       in
                                    quant qx uu____1125  in
                                  (FStar_Parser_Const.op_Minus, uu____1106)
                                   in
                                let uu____1144 =
                                  let uu____1167 =
                                    let uu____1188 =
                                      let uu____1207 =
                                        let uu____1208 =
                                          let uu____1209 =
                                            let uu____1214 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1215 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1214, uu____1215)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1209
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1208
                                         in
                                      quant xy uu____1207  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1188)
                                     in
                                  let uu____1232 =
                                    let uu____1255 =
                                      let uu____1276 =
                                        let uu____1295 =
                                          let uu____1296 =
                                            let uu____1297 =
                                              let uu____1302 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1303 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1302, uu____1303)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1297
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1296
                                           in
                                        quant xy uu____1295  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1276)
                                       in
                                    let uu____1320 =
                                      let uu____1343 =
                                        let uu____1364 =
                                          let uu____1383 =
                                            let uu____1384 =
                                              let uu____1385 =
                                                let uu____1390 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1391 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1390, uu____1391)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1385
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1384
                                             in
                                          quant xy uu____1383  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1364)
                                         in
                                      let uu____1408 =
                                        let uu____1431 =
                                          let uu____1452 =
                                            let uu____1471 =
                                              let uu____1472 =
                                                let uu____1473 =
                                                  let uu____1478 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1479 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1478, uu____1479)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1473
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1472
                                               in
                                            quant xy uu____1471  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1452)
                                           in
                                        let uu____1496 =
                                          let uu____1519 =
                                            let uu____1540 =
                                              let uu____1559 =
                                                let uu____1560 =
                                                  let uu____1561 =
                                                    let uu____1566 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1567 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1566, uu____1567)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1561
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1560
                                                 in
                                              quant xy uu____1559  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1540)
                                             in
                                          let uu____1584 =
                                            let uu____1607 =
                                              let uu____1628 =
                                                let uu____1647 =
                                                  let uu____1648 =
                                                    let uu____1649 =
                                                      let uu____1654 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1655 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1654,
                                                        uu____1655)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1649
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1648
                                                   in
                                                quant xy uu____1647  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1628)
                                               in
                                            let uu____1672 =
                                              let uu____1695 =
                                                let uu____1716 =
                                                  let uu____1735 =
                                                    let uu____1736 =
                                                      let uu____1737 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1737
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1736
                                                     in
                                                  quant qx uu____1735  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1716)
                                                 in
                                              [uu____1695]  in
                                            uu____1607 :: uu____1672  in
                                          uu____1519 :: uu____1584  in
                                        uu____1431 :: uu____1496  in
                                      uu____1343 :: uu____1408  in
                                    uu____1255 :: uu____1320  in
                                  uu____1167 :: uu____1232  in
                                uu____1085 :: uu____1144  in
                              uu____997 :: uu____1062  in
                            uu____909 :: uu____974  in
                          uu____821 :: uu____886  in
                        uu____733 :: uu____798  in
                      uu____645 :: uu____710  in
                    uu____563 :: uu____622  in
                  uu____482 :: uu____540  in
                let mk1 l v1 =
                  let uu____2096 =
                    let uu____2108 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2198  ->
                              match uu____2198 with
                              | (l',uu____2219) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2108
                      (FStar_Option.map
                         (fun uu____2318  ->
                            match uu____2318 with
                            | (uu____2346,b) ->
                                let uu____2380 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2380 v1))
                     in
                  FStar_All.pipe_right uu____2096 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2463  ->
                          match uu____2463 with
                          | (l',uu____2484) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
          FStar_SMTEncoding_Term.decl)
  =
  fun rng  ->
    fun env  ->
      fun tapp  ->
        fun vars  ->
          let uu____2552 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2552 with
          | (xxsym,xx) ->
              let uu____2563 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2563 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2579 =
                     let uu____2587 =
                       let uu____2588 =
                         let uu____2599 =
                           let uu____2600 =
                             let uu____2605 =
                               let uu____2606 =
                                 let uu____2611 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2611)  in
                               FStar_SMTEncoding_Util.mkEq uu____2606  in
                             (xx_has_type, uu____2605)  in
                           FStar_SMTEncoding_Util.mkImp uu____2600  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2599)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2588  in
                     let uu____2636 =
                       let uu____2638 =
                         let uu____2640 =
                           let uu____2642 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2642  in
                         Prims.strcat module_name uu____2640  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2638
                        in
                     (uu____2587, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2636)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2579)
  
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
    let uu____2705 =
      let uu____2706 =
        let uu____2714 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2714, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2706  in
    let uu____2719 =
      let uu____2722 =
        let uu____2723 =
          let uu____2731 =
            let uu____2732 =
              let uu____2743 =
                let uu____2744 =
                  let uu____2749 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2749)  in
                FStar_SMTEncoding_Util.mkImp uu____2744  in
              ([[typing_pred]], [xx], uu____2743)  in
            let uu____2768 =
              let uu____2783 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2783  in
            uu____2768 uu____2732  in
          (uu____2731, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2723  in
      [uu____2722]  in
    uu____2705 :: uu____2719  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2816 =
      let uu____2817 =
        let uu____2825 =
          let uu____2826 = FStar_TypeChecker_Env.get_range env  in
          let uu____2827 =
            let uu____2838 =
              let uu____2843 =
                let uu____2846 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2846]  in
              [uu____2843]  in
            let uu____2851 =
              let uu____2852 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2852 tt  in
            (uu____2838, [bb], uu____2851)  in
          FStar_SMTEncoding_Term.mkForall uu____2826 uu____2827  in
        (uu____2825, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2817  in
    let uu____2871 =
      let uu____2874 =
        let uu____2875 =
          let uu____2883 =
            let uu____2884 =
              let uu____2895 =
                let uu____2896 =
                  let uu____2901 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2901)  in
                FStar_SMTEncoding_Util.mkImp uu____2896  in
              ([[typing_pred]], [xx], uu____2895)  in
            let uu____2922 =
              let uu____2937 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2937  in
            uu____2922 uu____2884  in
          (uu____2883, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2875  in
      [uu____2874]  in
    uu____2816 :: uu____2871  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____2961 =
        let uu____2967 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____2967, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____2961  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____2991 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2991  in
    let uu____2996 =
      let uu____2997 =
        let uu____3005 =
          let uu____3006 = FStar_TypeChecker_Env.get_range env  in
          let uu____3007 =
            let uu____3018 =
              let uu____3023 =
                let uu____3026 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3026]  in
              [uu____3023]  in
            let uu____3031 =
              let uu____3032 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3032 tt  in
            (uu____3018, [bb], uu____3031)  in
          FStar_SMTEncoding_Term.mkForall uu____3006 uu____3007  in
        (uu____3005, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2997  in
    let uu____3051 =
      let uu____3054 =
        let uu____3055 =
          let uu____3063 =
            let uu____3064 =
              let uu____3075 =
                let uu____3076 =
                  let uu____3081 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3081)  in
                FStar_SMTEncoding_Util.mkImp uu____3076  in
              ([[typing_pred]], [xx], uu____3075)  in
            let uu____3102 =
              let uu____3117 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3117  in
            uu____3102 uu____3064  in
          (uu____3063, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3055  in
      let uu____3122 =
        let uu____3125 =
          let uu____3126 =
            let uu____3134 =
              let uu____3135 =
                let uu____3146 =
                  let uu____3147 =
                    let uu____3152 =
                      let uu____3153 =
                        let uu____3156 =
                          let uu____3159 =
                            let uu____3162 =
                              let uu____3163 =
                                let uu____3168 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3169 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3168, uu____3169)  in
                              FStar_SMTEncoding_Util.mkGT uu____3163  in
                            let uu____3171 =
                              let uu____3174 =
                                let uu____3175 =
                                  let uu____3180 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3181 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3180, uu____3181)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3175  in
                              let uu____3183 =
                                let uu____3186 =
                                  let uu____3187 =
                                    let uu____3192 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3193 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3192, uu____3193)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3187  in
                                [uu____3186]  in
                              uu____3174 :: uu____3183  in
                            uu____3162 :: uu____3171  in
                          typing_pred_y :: uu____3159  in
                        typing_pred :: uu____3156  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3153  in
                    (uu____3152, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3147  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3146)
                 in
              let uu____3217 =
                let uu____3232 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3232  in
              uu____3217 uu____3135  in
            (uu____3134,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3126  in
        [uu____3125]  in
      uu____3054 :: uu____3122  in
    uu____2996 :: uu____3051  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3265 =
      let uu____3266 =
        let uu____3274 =
          let uu____3275 = FStar_TypeChecker_Env.get_range env  in
          let uu____3276 =
            let uu____3287 =
              let uu____3292 =
                let uu____3295 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3295]  in
              [uu____3292]  in
            let uu____3300 =
              let uu____3301 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3301 tt  in
            (uu____3287, [bb], uu____3300)  in
          FStar_SMTEncoding_Term.mkForall uu____3275 uu____3276  in
        (uu____3274, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3266  in
    let uu____3320 =
      let uu____3323 =
        let uu____3324 =
          let uu____3332 =
            let uu____3333 =
              let uu____3344 =
                let uu____3345 =
                  let uu____3350 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3350)  in
                FStar_SMTEncoding_Util.mkImp uu____3345  in
              ([[typing_pred]], [xx], uu____3344)  in
            let uu____3371 =
              let uu____3386 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3386  in
            uu____3371 uu____3333  in
          (uu____3332, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3324  in
      [uu____3323]  in
    uu____3265 :: uu____3320  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3414 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3414]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3442 =
      let uu____3443 =
        let uu____3451 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3451, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3443  in
    [uu____3442]  in
  let mk_and_interp env conj uu____3472 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3511 =
      let uu____3512 =
        let uu____3520 =
          let uu____3521 = FStar_TypeChecker_Env.get_range env  in
          let uu____3522 =
            let uu____3533 =
              let uu____3534 =
                let uu____3539 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3539, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3534  in
            ([[l_and_a_b]], [aa; bb], uu____3533)  in
          FStar_SMTEncoding_Term.mkForall uu____3521 uu____3522  in
        (uu____3520, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3512  in
    [uu____3511]  in
  let mk_or_interp env disj uu____3583 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3622 =
      let uu____3623 =
        let uu____3631 =
          let uu____3632 = FStar_TypeChecker_Env.get_range env  in
          let uu____3633 =
            let uu____3644 =
              let uu____3645 =
                let uu____3650 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3650, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3645  in
            ([[l_or_a_b]], [aa; bb], uu____3644)  in
          FStar_SMTEncoding_Term.mkForall uu____3632 uu____3633  in
        (uu____3631, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3623  in
    [uu____3622]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3732 =
      let uu____3733 =
        let uu____3741 =
          let uu____3742 = FStar_TypeChecker_Env.get_range env  in
          let uu____3743 =
            let uu____3754 =
              let uu____3755 =
                let uu____3760 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3760, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3755  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3754)  in
          FStar_SMTEncoding_Term.mkForall uu____3742 uu____3743  in
        (uu____3741, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3733  in
    [uu____3732]  in
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
    let uu____3856 =
      let uu____3857 =
        let uu____3865 =
          let uu____3866 = FStar_TypeChecker_Env.get_range env  in
          let uu____3867 =
            let uu____3878 =
              let uu____3879 =
                let uu____3884 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3884, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3879  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3878)  in
          FStar_SMTEncoding_Term.mkForall uu____3866 uu____3867  in
        (uu____3865, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3857  in
    [uu____3856]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3977 =
      let uu____3978 =
        let uu____3986 =
          let uu____3987 = FStar_TypeChecker_Env.get_range env  in
          let uu____3988 =
            let uu____3999 =
              let uu____4000 =
                let uu____4005 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____4005, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4000  in
            ([[l_imp_a_b]], [aa; bb], uu____3999)  in
          FStar_SMTEncoding_Term.mkForall uu____3987 uu____3988  in
        (uu____3986, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3978  in
    [uu____3977]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____4088 =
      let uu____4089 =
        let uu____4097 =
          let uu____4098 = FStar_TypeChecker_Env.get_range env  in
          let uu____4099 =
            let uu____4110 =
              let uu____4111 =
                let uu____4116 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4116, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4111  in
            ([[l_iff_a_b]], [aa; bb], uu____4110)  in
          FStar_SMTEncoding_Term.mkForall uu____4098 uu____4099  in
        (uu____4097, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4089  in
    [uu____4088]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4181 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4181  in
    let uu____4186 =
      let uu____4187 =
        let uu____4195 =
          let uu____4196 = FStar_TypeChecker_Env.get_range env  in
          let uu____4197 =
            let uu____4208 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4208)  in
          FStar_SMTEncoding_Term.mkForall uu____4196 uu____4197  in
        (uu____4195, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4187  in
    [uu____4186]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4253 =
      let uu____4254 =
        let uu____4262 =
          let uu____4263 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4263 range_ty  in
        let uu____4264 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4262, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4264)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4254  in
    [uu____4253]  in
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
        let uu____4318 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4318 x1 t  in
      let uu____4320 = FStar_TypeChecker_Env.get_range env  in
      let uu____4321 =
        let uu____4332 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4332)  in
      FStar_SMTEncoding_Term.mkForall uu____4320 uu____4321  in
    let uu____4351 =
      let uu____4352 =
        let uu____4360 =
          let uu____4361 = FStar_TypeChecker_Env.get_range env  in
          let uu____4362 =
            let uu____4373 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4373)  in
          FStar_SMTEncoding_Term.mkForall uu____4361 uu____4362  in
        (uu____4360,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4352  in
    [uu____4351]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4436 =
      let uu____4437 =
        let uu____4445 =
          let uu____4446 = FStar_TypeChecker_Env.get_range env  in
          let uu____4447 =
            let uu____4463 =
              let uu____4464 =
                let uu____4469 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4470 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4469, uu____4470)  in
              FStar_SMTEncoding_Util.mkAnd uu____4464  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4463)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4446 uu____4447  in
        (uu____4445,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4437  in
    [uu____4436]  in
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
          let uu____4991 =
            FStar_Util.find_opt
              (fun uu____5029  ->
                 match uu____5029 with
                 | (l,uu____5045) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4991 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____5088,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5149 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5149 with
        | (form,decls) ->
            let uu____5158 =
              let uu____5161 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5161]  in
            FStar_List.append decls uu____5158
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list *
                FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____5218 =
                ((let uu____5222 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5222) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5218
              then
                let arg_sorts =
                  let uu____5236 =
                    let uu____5237 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5237.FStar_Syntax_Syntax.n  in
                  match uu____5236 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5243) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5281  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5288 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5290 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5290 with
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
                (let uu____5332 = prims.is lid  in
                 if uu____5332
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5343 = prims.mk lid vname  in
                   match uu____5343 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5377 =
                      let uu____5396 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5396 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5424 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5424
                            then
                              let uu____5429 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___383_5432 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___383_5432.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___383_5432.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___383_5432.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___383_5432.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___383_5432.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___383_5432.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___383_5432.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___383_5432.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___383_5432.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___383_5432.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___383_5432.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___383_5432.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___383_5432.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___383_5432.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___383_5432.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___383_5432.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___383_5432.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___383_5432.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___383_5432.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___383_5432.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___383_5432.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___383_5432.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___383_5432.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___383_5432.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___383_5432.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___383_5432.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___383_5432.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___383_5432.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___383_5432.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___383_5432.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___383_5432.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___383_5432.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___383_5432.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___383_5432.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___383_5432.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___383_5432.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___383_5432.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___383_5432.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___383_5432.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___383_5432.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___383_5432.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___383_5432.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5429
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5455 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5455)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5377 with
                    | (formals,(pre_opt,res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___373_5578  ->
                                  match uu___373_5578 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____5582 = FStar_Util.prefix vars
                                         in
                                      (match uu____5582 with
                                       | (uu____5606,(xxsym,uu____5608)) ->
                                           let xx =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (xxsym,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           let uu____5632 =
                                             let uu____5633 =
                                               let uu____5641 =
                                                 let uu____5642 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5643 =
                                                   let uu____5654 =
                                                     let uu____5655 =
                                                       let uu____5660 =
                                                         let uu____5661 =
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             (FStar_SMTEncoding_Env.escape
                                                                d.FStar_Ident.str)
                                                             xx
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____5661
                                                          in
                                                       (vapp, uu____5660)  in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____5655
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5654)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5642 uu____5643
                                                  in
                                               (uu____5641,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 (Prims.strcat
                                                    "disc_equation_"
                                                    (FStar_SMTEncoding_Env.escape
                                                       d.FStar_Ident.str)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5633
                                              in
                                           [uu____5632])
                                  | FStar_Syntax_Syntax.Projector (d,f) ->
                                      let uu____5676 = FStar_Util.prefix vars
                                         in
                                      (match uu____5676 with
                                       | (uu____5700,(xxsym,uu____5702)) ->
                                           let xx =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (xxsym,
                                                 FStar_SMTEncoding_Term.Term_sort)
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
                                           let uu____5734 =
                                             let uu____5735 =
                                               let uu____5743 =
                                                 let uu____5744 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv
                                                    in
                                                 let uu____5745 =
                                                   let uu____5756 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app)
                                                      in
                                                   ([[vapp]], vars,
                                                     uu____5756)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____5744 uu____5745
                                                  in
                                               (uu____5743,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.strcat
                                                    "proj_equation_" tp_name))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5735
                                              in
                                           [uu____5734])
                                  | uu____5769 -> []))
                           in
                        let uu____5770 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env
                           in
                        (match uu____5770 with
                         | (vars,guards,env',decls1,uu____5797) ->
                             let uu____5810 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____5823 =
                                     FStar_SMTEncoding_Util.mk_and_l guards
                                      in
                                   (uu____5823, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____5827 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env'
                                      in
                                   (match uu____5827 with
                                    | (g,ds) ->
                                        let uu____5840 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards)
                                           in
                                        (uu____5840,
                                          (FStar_List.append decls1 ds)))
                                in
                             (match uu____5810 with
                              | (guard,decls11) ->
                                  let dummy_var =
                                    ("@dummy",
                                      FStar_SMTEncoding_Term.dummy_sort)
                                     in
                                  let dummy_tm =
                                    FStar_SMTEncoding_Term.mkFreeV dummy_var
                                      FStar_Range.dummyRange
                                     in
                                  let should_thunk =
                                    let is_type1 t =
                                      let uu____5873 =
                                        let uu____5874 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____5874.FStar_Syntax_Syntax.n  in
                                      match uu____5873 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____5878 -> true
                                      | uu____5880 -> false  in
                                    (((lid.FStar_Ident.nsstr <> "Prims") &&
                                        (let uu____5885 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic)
                                            in
                                         Prims.op_Negation uu____5885))
                                       &&
                                       (let uu____5891 =
                                          let uu____5893 =
                                            FStar_Syntax_Util.is_squash
                                              t_norm
                                             in
                                          FStar_Option.isSome uu____5893  in
                                        Prims.op_Negation uu____5891))
                                      &&
                                      (let uu____5909 = is_type1 t_norm  in
                                       Prims.op_Negation uu____5909)
                                     in
                                  let uu____5911 =
                                    match vars with
                                    | [] when should_thunk ->
                                        (true, [dummy_var])
                                    | uu____5955 -> (false, vars)  in
                                  (match uu____5911 with
                                   | (thunked,vars1) ->
                                       let arity = FStar_List.length formals
                                          in
                                       let uu____5998 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked
                                          in
                                       (match uu____5998 with
                                        | (vname,vtok_opt,env1) ->
                                            let get_vtok uu____6036 =
                                              FStar_Option.get vtok_opt  in
                                            let vtok_tm =
                                              match (formals, vtok_opt) with
                                              | ([],uu____6050) when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (vname,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                              | uu____6072 when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____6091 ->
                                                  let uu____6107 =
                                                    let uu____6115 =
                                                      get_vtok ()  in
                                                    (uu____6115, [])  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6107
                                               in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1
                                               in
                                            let vapp =
                                              let uu____6122 =
                                                let uu____6130 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1
                                                   in
                                                (vname, uu____6130)  in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____6122
                                               in
                                            let uu____6141 =
                                              let vname_decl =
                                                let uu____6149 =
                                                  let uu____6161 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.snd)
                                                     in
                                                  (vname, uu____6161,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____6149
                                                 in
                                              let uu____6183 =
                                                let env2 =
                                                  let uu___384_6189 = env1
                                                     in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.cache
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.cache);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___384_6189.FStar_SMTEncoding_Env.encoding_quantifier)
                                                  }  in
                                                let uu____6190 =
                                                  let uu____6192 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt
                                                     in
                                                  Prims.op_Negation
                                                    uu____6192
                                                   in
                                                if uu____6190
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm
                                                 in
                                              match uu____6183 with
                                              | (tok_typing,decls2) ->
                                                  let uu____6209 =
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
                                                        let uu____6232 =
                                                          let uu____6233 =
                                                            let uu____6236 =
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                                (vname,
                                                                  FStar_SMTEncoding_Term.Term_sort)
                                                               in
                                                            FStar_All.pipe_left
                                                              (fun _0_1  ->
                                                                 FStar_Pervasives_Native.Some
                                                                   _0_1)
                                                              uu____6236
                                                             in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____6233
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [tok_typing1]),
                                                          uu____6232)
                                                    | uu____6246 when thunked
                                                        -> (decls2, env1)
                                                    | uu____6256 ->
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
                                                          let uu____6277 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv
                                                             in
                                                          let uu____6278 =
                                                            let uu____6289 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp)
                                                               in
                                                            ([[pat]], vars1,
                                                              uu____6289)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____6277
                                                            uu____6278
                                                           in
                                                        let name_tok_corr =
                                                          let uu____6299 =
                                                            let uu____6307 =
                                                              name_tok_corr_formula
                                                                vtok_app
                                                               in
                                                            (uu____6307,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.strcat
                                                                 "token_correspondence_"
                                                                 vname))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____6299
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
                                                          let vtok_app_r =
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f
                                                              [(vtok,
                                                                 FStar_SMTEncoding_Term.Term_sort)]
                                                             in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____6335 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6336 =
                                                              let uu____6347
                                                                =
                                                                let uu____6348
                                                                  =
                                                                  let uu____6353
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing
                                                                     in
                                                                  let uu____6354
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp  in
                                                                  (uu____6353,
                                                                    uu____6354)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____6348
                                                                 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____6347)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6335
                                                              uu____6336
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.strcat
                                                                 "function_token_typing_"
                                                                 vname))
                                                           in
                                                        ((FStar_List.append
                                                            decls2
                                                            [vtok_decl;
                                                            name_tok_corr;
                                                            tok_typing1]),
                                                          env1)
                                                     in
                                                  (match uu____6209 with
                                                   | (tok_decl,env2) ->
                                                       ((vname_decl ::
                                                         tok_decl), env2))
                                               in
                                            (match uu____6141 with
                                             | (decls2,env2) ->
                                                 let uu____6405 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t
                                                      in
                                                   let uu____6415 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env'
                                                      in
                                                   match uu____6415 with
                                                   | (encoded_res_t,decls) ->
                                                       let uu____6430 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t
                                                          in
                                                       (encoded_res_t,
                                                         uu____6430, decls)
                                                    in
                                                 (match uu____6405 with
                                                  | (encoded_res_t,ty_pred,decls3)
                                                      ->
                                                      let typingAx =
                                                        let uu____6447 =
                                                          let uu____6455 =
                                                            let uu____6456 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6457 =
                                                              let uu____6468
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred)
                                                                 in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____6468)
                                                               in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____6456
                                                              uu____6457
                                                             in
                                                          (uu____6455,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.strcat
                                                               "typing_"
                                                               vname))
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6447
                                                         in
                                                      let freshness =
                                                        let uu____6484 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New)
                                                           in
                                                        if uu____6484
                                                        then
                                                          let uu____6492 =
                                                            let uu____6493 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv
                                                               in
                                                            let uu____6494 =
                                                              let uu____6507
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              let uu____6525
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  ()
                                                                 in
                                                              (vname,
                                                                uu____6507,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____6525)
                                                               in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____6493
                                                              uu____6494
                                                             in
                                                          let uu____6531 =
                                                            let uu____6534 =
                                                              let uu____6535
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv
                                                                 in
                                                              pretype_axiom
                                                                uu____6535
                                                                env2 vapp
                                                                vars1
                                                               in
                                                            [uu____6534]  in
                                                          uu____6492 ::
                                                            uu____6531
                                                        else []  in
                                                      let g =
                                                        let uu____6541 =
                                                          let uu____6544 =
                                                            let uu____6547 =
                                                              let uu____6550
                                                                =
                                                                let uu____6553
                                                                  =
                                                                  mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1
                                                                   in
                                                                typingAx ::
                                                                  uu____6553
                                                                 in
                                                              FStar_List.append
                                                                freshness
                                                                uu____6550
                                                               in
                                                            FStar_List.append
                                                              decls3
                                                              uu____6547
                                                             in
                                                          FStar_List.append
                                                            decls2 uu____6544
                                                           in
                                                        FStar_List.append
                                                          decls11 uu____6541
                                                         in
                                                      (g, env2)))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl
            Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____6595 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6595 with
          | FStar_Pervasives_Native.None  ->
              let uu____6606 = encode_free_var false env x t t_norm []  in
              (match uu____6606 with
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
            (FStar_SMTEncoding_Term.decl Prims.list *
              FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____6677 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6677 with
            | (decls,env1) ->
                let uu____6696 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6696
                then
                  let uu____6705 =
                    let uu____6708 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6708  in
                  (uu____6705, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____6768  ->
                fun lb  ->
                  match uu____6768 with
                  | (decls,env1) ->
                      let uu____6788 =
                        let uu____6795 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____6795
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____6788 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____6828 = FStar_Syntax_Util.head_and_args t  in
    match uu____6828 with
    | (hd1,args) ->
        let uu____6872 =
          let uu____6873 = FStar_Syntax_Util.un_uinst hd1  in
          uu____6873.FStar_Syntax_Syntax.n  in
        (match uu____6872 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____6879,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____6903 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____6914 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___385_6922 = en  in
    let uu____6923 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___385_6922.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___385_6922.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___385_6922.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___385_6922.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___385_6922.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____6923;
      FStar_SMTEncoding_Env.nolabels =
        (uu___385_6922.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___385_6922.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___385_6922.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___385_6922.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___385_6922.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____6955  ->
      fun quals  ->
        match uu____6955 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7062 = FStar_Util.first_N nbinders formals  in
              match uu____7062 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7163  ->
                         fun uu____7164  ->
                           match (uu____7163, uu____7164) with
                           | ((formal,uu____7190),(binder,uu____7192)) ->
                               let uu____7213 =
                                 let uu____7220 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7220)  in
                               FStar_Syntax_Syntax.NT uu____7213) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7234 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7275  ->
                              match uu____7275 with
                              | (x,i) ->
                                  let uu____7294 =
                                    let uu___386_7295 = x  in
                                    let uu____7296 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_7295.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_7295.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7296
                                    }  in
                                  (uu____7294, i)))
                       in
                    FStar_All.pipe_right uu____7234
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7320 =
                      let uu____7325 = FStar_Syntax_Subst.compress body  in
                      let uu____7326 =
                        let uu____7327 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7327
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7325 uu____7326
                       in
                    uu____7320 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function t e =
              let tcenv =
                let uu___387_7378 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___387_7378.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___387_7378.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___387_7378.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___387_7378.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___387_7378.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___387_7378.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___387_7378.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___387_7378.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___387_7378.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___387_7378.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___387_7378.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___387_7378.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___387_7378.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___387_7378.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___387_7378.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___387_7378.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___387_7378.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___387_7378.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___387_7378.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___387_7378.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___387_7378.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___387_7378.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___387_7378.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___387_7378.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___387_7378.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___387_7378.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___387_7378.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___387_7378.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___387_7378.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___387_7378.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___387_7378.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___387_7378.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___387_7378.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___387_7378.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___387_7378.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___387_7378.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___387_7378.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___387_7378.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___387_7378.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___387_7378.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___387_7378.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___387_7378.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7450  ->
                       fun uu____7451  ->
                         match (uu____7450, uu____7451) with
                         | ((x,uu____7477),(b,uu____7479)) ->
                             let uu____7500 =
                               let uu____7507 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7507)  in
                             FStar_Syntax_Syntax.NT uu____7500) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7532 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7532
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7561 ->
                    let uu____7568 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7568
                | uu____7569 when Prims.op_Negation norm1 ->
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
                | uu____7572 ->
                    let uu____7573 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7573)
                 in
              let aux t1 e1 =
                let uu____7615 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7615 with
                | (binders,body,lopt) ->
                    let uu____7647 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7663 -> arrow_formals_comp_norm false t1  in
                    (match uu____7647 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7697 =
                           if nformals < nbinders
                           then
                             let uu____7741 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7741 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____7825 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____7825)
                           else
                             if nformals > nbinders
                             then
                               (let uu____7865 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____7865 with
                                | (binders1,body1) ->
                                    let uu____7918 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____7918))
                             else
                               (let uu____7931 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____7931))
                            in
                         (match uu____7697 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____7991 = aux t e  in
              match uu____7991 with
              | (binders,body,comp) ->
                  let uu____8037 =
                    let uu____8048 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____8048
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____8063 = aux comp1 body1  in
                      match uu____8063 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____8037 with
                   | (binders1,body1,comp1) ->
                       let uu____8146 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____8146, comp1))
               in
            (try
               (fun uu___389_8173  ->
                  match () with
                  | () ->
                      let uu____8180 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8180
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8196 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8259  ->
                                   fun lb  ->
                                     match uu____8259 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8314 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8314
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8320 =
                                             let uu____8329 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8329
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8320 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8196 with
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
                                    FStar_Syntax_Syntax.lbtyp = uu____8470;
                                    FStar_Syntax_Syntax.lbeff = uu____8471;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8473;
                                    FStar_Syntax_Syntax.lbpos = uu____8474;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8498 =
                                     let uu____8505 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8505 with
                                     | (tcenv',uu____8521,e_t) ->
                                         let uu____8527 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8538 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8527 with
                                          | (e1,t_norm1) ->
                                              ((let uu___390_8555 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___390_8555.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8498 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8565 =
                                          destruct_bound_function t_norm1 e1
                                           in
                                        (match uu____8565 with
                                         | (binders,body,t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8585 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8585
                                               then
                                                 let uu____8590 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8593 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8590 uu____8593
                                               else ());
                                              (let uu____8598 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8598 with
                                               | (vars,_guards,env'1,binder_decls,uu____8625)
                                                   ->
                                                   let app =
                                                     let uu____8639 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     let uu____8640 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars
                                                        in
                                                     FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                       uu____8639 fvb
                                                       uu____8640
                                                      in
                                                   let uu____8643 =
                                                     let is_logical =
                                                       let uu____8656 =
                                                         let uu____8657 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____8657.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____8656 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____8663 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____8667 =
                                                         let uu____8668 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____8668
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____8667
                                                         (fun lid  ->
                                                            let uu____8677 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____8677
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____8678 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____8678
                                                     then
                                                       let uu____8694 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____8695 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body env'1
                                                          in
                                                       (app, uu____8694,
                                                         uu____8695)
                                                     else
                                                       (let uu____8706 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body env'1
                                                           in
                                                        (app, app,
                                                          uu____8706))
                                                      in
                                                   (match uu____8643 with
                                                    | (pat,app1,(body1,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____8730 =
                                                            let uu____8738 =
                                                              let uu____8739
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8740
                                                                =
                                                                let uu____8751
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____8751)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8739
                                                                uu____8740
                                                               in
                                                            let uu____8760 =
                                                              let uu____8761
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8761
                                                               in
                                                            (uu____8738,
                                                              uu____8760,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8730
                                                           in
                                                        let uu____8767 =
                                                          let uu____8770 =
                                                            let uu____8773 =
                                                              let uu____8776
                                                                =
                                                                let uu____8779
                                                                  =
                                                                  primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1
                                                                   in
                                                                FStar_List.append
                                                                  [eqn]
                                                                  uu____8779
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____8776
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____8773
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____8770
                                                           in
                                                        (uu____8767, env2))))))
                               | uu____8784 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____8849 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____8849,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____8855 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____8908  ->
                                         fun fvb  ->
                                           match uu____8908 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____8963 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8963
                                                  in
                                               let gtok =
                                                 let uu____8967 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8967
                                                  in
                                               let env4 =
                                                 let uu____8970 =
                                                   let uu____8973 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____8973
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____8970
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____8855 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9100
                                     t_norm uu____9102 =
                                     match (uu____9100, uu____9102) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9134;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9135;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9137;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9138;_})
                                         ->
                                         let uu____9165 =
                                           let uu____9172 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9172 with
                                           | (tcenv',uu____9188,e_t) ->
                                               let uu____9194 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9205 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9194 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___391_9222 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___391_9222.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9165 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9237 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9237
                                                then
                                                  let uu____9242 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9244 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9246 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9242 uu____9244
                                                    uu____9246
                                                else ());
                                               (let uu____9251 =
                                                  destruct_bound_function
                                                    t_norm1 e1
                                                   in
                                                match uu____9251 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9280 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9280 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9304 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9304
                                                           then
                                                             let uu____9309 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9311 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9314 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9316 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9309
                                                               uu____9311
                                                               uu____9314
                                                               uu____9316
                                                           else ());
                                                          (let uu____9321 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9321
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9352)
                                                               ->
                                                               let uu____9365
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9378
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9378,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9382
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9382
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9395
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9395,
                                                                    decls0))
                                                                  in
                                                               (match uu____9365
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
                                                                    let uu____9418
                                                                    =
                                                                    let uu____9430
                                                                    =
                                                                    let uu____9433
                                                                    =
                                                                    let uu____9436
                                                                    =
                                                                    let uu____9439
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9439
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    uu____9436
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9433
                                                                     in
                                                                    (g,
                                                                    uu____9430,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9418
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
                                                                    let uu____9470
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9470
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
                                                                    let uu____9485
                                                                    =
                                                                    let uu____9488
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9488
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9485
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9494
                                                                    =
                                                                    let uu____9497
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9497
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9494
                                                                     in
                                                                    let uu____9502
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9502
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9520
                                                                    =
                                                                    let uu____9528
                                                                    =
                                                                    let uu____9529
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9530
                                                                    =
                                                                    let uu____9546
                                                                    =
                                                                    let uu____9547
                                                                    =
                                                                    let uu____9552
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9552)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9547
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9546)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9529
                                                                    uu____9530
                                                                     in
                                                                    let uu____9566
                                                                    =
                                                                    let uu____9567
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9567
                                                                     in
                                                                    (uu____9528,
                                                                    uu____9566,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9520
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9574
                                                                    =
                                                                    let uu____9582
                                                                    =
                                                                    let uu____9583
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9584
                                                                    =
                                                                    let uu____9595
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9595)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9583
                                                                    uu____9584
                                                                     in
                                                                    (uu____9582,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9574
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9609
                                                                    =
                                                                    let uu____9617
                                                                    =
                                                                    let uu____9618
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9619
                                                                    =
                                                                    let uu____9630
                                                                    =
                                                                    let uu____9631
                                                                    =
                                                                    let uu____9636
                                                                    =
                                                                    let uu____9637
                                                                    =
                                                                    let uu____9640
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9640
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9637
                                                                     in
                                                                    (gsapp,
                                                                    uu____9636)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9631
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9630)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9618
                                                                    uu____9619
                                                                     in
                                                                    (uu____9617,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9609
                                                                     in
                                                                    let uu____9654
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
                                                                    let uu____9666
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9666
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9668
                                                                    =
                                                                    let uu____9676
                                                                    =
                                                                    let uu____9677
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9678
                                                                    =
                                                                    let uu____9689
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9689)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9677
                                                                    uu____9678
                                                                     in
                                                                    (uu____9676,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9668
                                                                     in
                                                                    let uu____9702
                                                                    =
                                                                    let uu____9711
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____9711
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____9726
                                                                    =
                                                                    let uu____9729
                                                                    =
                                                                    let uu____9730
                                                                    =
                                                                    let uu____9738
                                                                    =
                                                                    let uu____9739
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9740
                                                                    =
                                                                    let uu____9751
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9751)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9739
                                                                    uu____9740
                                                                     in
                                                                    (uu____9738,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9730
                                                                     in
                                                                    [uu____9729]
                                                                     in
                                                                    (d3,
                                                                    uu____9726)
                                                                     in
                                                                    match uu____9702
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9654
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
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
                                                                    env02))))))))))
                                      in
                                   let uu____9814 =
                                     let uu____9827 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____9890  ->
                                          fun uu____9891  ->
                                            match (uu____9890, uu____9891)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10016 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10016 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____9827
                                      in
                                   (match uu____9814 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10089 =
                                          let isDeclFun uu___374_10104 =
                                            match uu___374_10104 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10106 -> true
                                            | uu____10119 -> false  in
                                          let uu____10121 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10121
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____10089 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10161 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___375_10167  ->
                                        match uu___375_10167 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10170 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10178 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10178)))
                                in
                             if uu____10161
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___393_10200  ->
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
                   let uu____10238 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10238
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
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____10308 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10308 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10314 = encode_sigelt' env se  in
      match uu____10314 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10326 =
                  let uu____10327 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____10327  in
                [uu____10326]
            | uu____10330 ->
                let uu____10331 =
                  let uu____10334 =
                    let uu____10335 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10335  in
                  uu____10334 :: g  in
                let uu____10338 =
                  let uu____10341 =
                    let uu____10342 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10342  in
                  [uu____10341]  in
                FStar_List.append uu____10331 uu____10338
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____10358 =
          let uu____10359 = FStar_Syntax_Subst.compress t  in
          uu____10359.FStar_Syntax_Syntax.n  in
        match uu____10358 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10364)) -> s = "opaque_to_smt"
        | uu____10369 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____10378 =
          let uu____10379 = FStar_Syntax_Subst.compress t  in
          uu____10379.FStar_Syntax_Syntax.n  in
        match uu____10378 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10384)) -> s = "uninterpreted_by_smt"
        | uu____10389 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10395 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____10401 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____10413 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____10414 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10415 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10428 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10430 =
            let uu____10432 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____10432  in
          if uu____10430
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____10461 ->
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
               let uu____10493 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____10493 with
               | (formals,uu____10513) ->
                   let arity = FStar_List.length formals  in
                   let uu____10537 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____10537 with
                    | (aname,atok,env2) ->
                        let uu____10563 =
                          let uu____10568 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____10568 env2
                           in
                        (match uu____10563 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____10580 =
                                 let uu____10581 =
                                   let uu____10593 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____10613  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____10593,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____10581
                                  in
                               [uu____10580;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____10630 =
                               let aux uu____10691 uu____10692 =
                                 match (uu____10691, uu____10692) with
                                 | ((bv,uu____10751),(env3,acc_sorts,acc)) ->
                                     let uu____10798 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____10798 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____10630 with
                              | (uu____10882,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____10908 =
                                      let uu____10916 =
                                        let uu____10917 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10918 =
                                          let uu____10929 =
                                            let uu____10930 =
                                              let uu____10935 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____10935)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____10930
                                             in
                                          ([[app]], xs_sorts, uu____10929)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10917 uu____10918
                                         in
                                      (uu____10916,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10908
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
                                    let uu____10952 =
                                      let uu____10960 =
                                        let uu____10961 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10962 =
                                          let uu____10973 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____10973)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10961 uu____10962
                                         in
                                      (uu____10960,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10952
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____10988 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____10988 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11014,uu____11015)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____11016 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____11016 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11038,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____11045 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___376_11051  ->
                      match uu___376_11051 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____11054 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____11060 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11063 -> false))
               in
            Prims.op_Negation uu____11045  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____11073 =
               let uu____11080 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____11080 env fv t quals  in
             match uu____11073 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____11099 =
                   let uu____11100 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____11100  in
                 (uu____11099, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____11106 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____11106 with
           | (uvs,f1) ->
               let env1 =
                 let uu___394_11118 = env  in
                 let uu____11119 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___394_11118.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___394_11118.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___394_11118.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____11119;
                   FStar_SMTEncoding_Env.warn =
                     (uu___394_11118.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___394_11118.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___394_11118.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___394_11118.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___394_11118.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___394_11118.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___394_11118.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____11121 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____11121 with
                | (f3,decls) ->
                    let g =
                      let uu____11135 =
                        let uu____11136 =
                          let uu____11144 =
                            let uu____11145 =
                              let uu____11147 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____11147
                               in
                            FStar_Pervasives_Native.Some uu____11145  in
                          let uu____11151 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____11144, uu____11151)  in
                        FStar_SMTEncoding_Util.mkAssume uu____11136  in
                      [uu____11135]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____11156) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____11170 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____11192 =
                       let uu____11195 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____11195.FStar_Syntax_Syntax.fv_name  in
                     uu____11192.FStar_Syntax_Syntax.v  in
                   let uu____11196 =
                     let uu____11198 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____11198  in
                   if uu____11196
                   then
                     let val_decl =
                       let uu___395_11230 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___395_11230.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___395_11230.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___395_11230.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____11231 = encode_sigelt' env1 val_decl  in
                     match uu____11231 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____11170 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____11267,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____11269;
                          FStar_Syntax_Syntax.lbtyp = uu____11270;
                          FStar_Syntax_Syntax.lbeff = uu____11271;
                          FStar_Syntax_Syntax.lbdef = uu____11272;
                          FStar_Syntax_Syntax.lbattrs = uu____11273;
                          FStar_Syntax_Syntax.lbpos = uu____11274;_}::[]),uu____11275)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____11294 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____11294 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____11337 =
                   let uu____11340 =
                     let uu____11341 =
                       let uu____11349 =
                         let uu____11350 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____11351 =
                           let uu____11362 =
                             let uu____11363 =
                               let uu____11368 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____11368)  in
                             FStar_SMTEncoding_Util.mkEq uu____11363  in
                           ([[b2t_x]], [xx], uu____11362)  in
                         FStar_SMTEncoding_Term.mkForall uu____11350
                           uu____11351
                          in
                       (uu____11349,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11341  in
                   [uu____11340]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____11337
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____11400,uu____11401) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___377_11411  ->
                  match uu___377_11411 with
                  | FStar_Syntax_Syntax.Discriminator uu____11413 -> true
                  | uu____11415 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____11417,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____11429 =
                     let uu____11431 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____11431.FStar_Ident.idText  in
                   uu____11429 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___378_11438  ->
                     match uu___378_11438 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____11441 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11444) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___379_11458  ->
                  match uu___379_11458 with
                  | FStar_Syntax_Syntax.Projector uu____11460 -> true
                  | uu____11466 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____11470 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____11470 with
           | FStar_Pervasives_Native.Some uu____11477 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___396_11479 = se  in
                 let uu____11480 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____11480;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___396_11479.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___396_11479.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___396_11479.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11483) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11498) ->
          let uu____11507 = encode_sigelts env ses  in
          (match uu____11507 with
           | (g,env1) ->
               let uu____11524 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___380_11547  ->
                         match uu___380_11547 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____11549;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____11550;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____11551;_}
                             -> false
                         | uu____11558 -> true))
                  in
               (match uu____11524 with
                | (g',inversions) ->
                    let uu____11574 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___381_11595  ->
                              match uu___381_11595 with
                              | FStar_SMTEncoding_Term.DeclFun uu____11597 ->
                                  true
                              | uu____11610 -> false))
                       in
                    (match uu____11574 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____11627,tps,k,uu____11630,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___382_11649  ->
                    match uu___382_11649 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11653 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____11666 = c  in
              match uu____11666 with
              | (name,args,uu____11671,uu____11672,uu____11673) ->
                  let uu____11684 =
                    let uu____11685 =
                      let uu____11697 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____11724  ->
                                match uu____11724 with
                                | (uu____11733,sort,uu____11735) -> sort))
                         in
                      (name, uu____11697, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____11685  in
                  [uu____11684]
            else
              (let uu____11746 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____11746 c)
             in
          let inversion_axioms tapp vars =
            let uu____11774 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____11782 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____11782 FStar_Option.isNone))
               in
            if uu____11774
            then []
            else
              (let uu____11817 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____11817 with
               | (xxsym,xx) ->
                   let uu____11830 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____11869  ->
                             fun l  ->
                               match uu____11869 with
                               | (out,decls) ->
                                   let uu____11889 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____11889 with
                                    | (uu____11900,data_t) ->
                                        let uu____11902 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____11902 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____11946 =
                                                 let uu____11947 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____11947.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____11946 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____11950,indices) ->
                                                   indices
                                               | uu____11976 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____12006  ->
                                                         match uu____12006
                                                         with
                                                         | (x,uu____12014) ->
                                                             let uu____12019
                                                               =
                                                               let uu____12020
                                                                 =
                                                                 let uu____12028
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____12028,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____12020
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____12019)
                                                    env)
                                                in
                                             let uu____12033 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____12033 with
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
                                                      let uu____12063 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____12081
                                                                 =
                                                                 let uu____12086
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____12086,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____12081)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____12063
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____12089 =
                                                      let uu____12090 =
                                                        let uu____12095 =
                                                          let uu____12096 =
                                                            let uu____12101 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____12101,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____12096
                                                           in
                                                        (out, uu____12095)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____12090
                                                       in
                                                    (uu____12089,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____11830 with
                    | (data_ax,decls) ->
                        let uu____12114 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____12114 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____12131 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____12131 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____12138 =
                                 let uu____12146 =
                                   let uu____12147 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____12148 =
                                     let uu____12159 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____12172 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____12159,
                                       uu____12172)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____12147 uu____12148
                                    in
                                 let uu____12181 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____12146,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____12181)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____12138
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____12187 =
            let uu____12192 =
              let uu____12193 = FStar_Syntax_Subst.compress k  in
              uu____12193.FStar_Syntax_Syntax.n  in
            match uu____12192 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____12228 -> (tps, k)  in
          (match uu____12187 with
           | (formals,res) ->
               let uu____12235 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____12235 with
                | (formals1,res1) ->
                    let uu____12246 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____12246 with
                     | (vars,guards,env',binder_decls,uu____12271) ->
                         let arity = FStar_List.length vars  in
                         let uu____12285 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____12285 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____12315 =
                                  let uu____12323 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____12323)  in
                                FStar_SMTEncoding_Util.mkApp uu____12315  in
                              let uu____12329 =
                                let tname_decl =
                                  let uu____12339 =
                                    let uu____12340 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____12368  ->
                                              match uu____12368 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____12389 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____12340,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____12389, false)
                                     in
                                  constructor_or_logic_type_decl uu____12339
                                   in
                                let uu____12397 =
                                  match vars with
                                  | [] ->
                                      let uu____12410 =
                                        let uu____12411 =
                                          let uu____12414 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____12414
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____12411
                                         in
                                      ([], uu____12410)
                                  | uu____12426 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____12436 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____12436
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____12452 =
                                          let uu____12460 =
                                            let uu____12461 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____12462 =
                                              let uu____12478 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____12478)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____12461 uu____12462
                                             in
                                          (uu____12460,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____12452
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____12397 with
                                | (tok_decls,env2) ->
                                    let uu____12505 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____12505
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____12329 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____12533 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____12533 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____12555 =
                                               let uu____12556 =
                                                 let uu____12564 =
                                                   let uu____12565 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____12565
                                                    in
                                                 (uu____12564,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____12556
                                                in
                                             [uu____12555]
                                           else []  in
                                         let uu____12573 =
                                           let uu____12576 =
                                             let uu____12579 =
                                               let uu____12580 =
                                                 let uu____12588 =
                                                   let uu____12589 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____12590 =
                                                     let uu____12601 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____12601)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____12589 uu____12590
                                                    in
                                                 (uu____12588,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____12580
                                                in
                                             [uu____12579]  in
                                           FStar_List.append karr uu____12576
                                            in
                                         FStar_List.append decls1 uu____12573
                                      in
                                   let aux =
                                     let uu____12616 =
                                       let uu____12619 =
                                         inversion_axioms tapp vars  in
                                       let uu____12622 =
                                         let uu____12625 =
                                           let uu____12626 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____12626 env2
                                             tapp vars
                                            in
                                         [uu____12625]  in
                                       FStar_List.append uu____12619
                                         uu____12622
                                        in
                                     FStar_List.append kindingAx uu____12616
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____12631,uu____12632,uu____12633,uu____12634,uu____12635)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____12643,t,uu____12645,n_tps,uu____12647) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____12657 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____12657 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____12705 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____12705 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____12733 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____12733 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____12753 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____12753 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____12832 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____12832,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____12839 =
                                  let uu____12840 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____12840, true)
                                   in
                                let uu____12848 =
                                  let uu____12855 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____12855
                                   in
                                FStar_All.pipe_right uu____12839 uu____12848
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
                              let uu____12867 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____12867 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____12879::uu____12880 ->
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
                                         let uu____12939 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____12940 =
                                           let uu____12951 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____12951)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____12939 uu____12940
                                     | uu____12972 -> tok_typing  in
                                   let uu____12983 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____12983 with
                                    | (vars',guards',env'',decls_formals,uu____13008)
                                        ->
                                        let uu____13021 =
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
                                        (match uu____13021 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____13051 ->
                                                   let uu____13060 =
                                                     let uu____13061 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____13061
                                                      in
                                                   [uu____13060]
                                                in
                                             let encode_elim uu____13077 =
                                               let uu____13078 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____13078 with
                                               | (head1,args) ->
                                                   let uu____13129 =
                                                     let uu____13130 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____13130.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____13129 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____13142;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____13143;_},uu____13144)
                                                        ->
                                                        let encoded_head_fvb
                                                          =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____13150 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_args
                                                            args env'
                                                           in
                                                        (match uu____13150
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
                                                                 | uu____13204
                                                                    ->
                                                                    let uu____13205
                                                                    =
                                                                    let uu____13211
                                                                    =
                                                                    let uu____13213
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13213
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13211)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13205
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13233
                                                                    =
                                                                    let uu____13235
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13235
                                                                     in
                                                                    if
                                                                    uu____13233
                                                                    then
                                                                    let uu____13251
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13251]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____13254
                                                               =
                                                               let uu____13268
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____13325
                                                                     ->
                                                                    fun
                                                                    uu____13326
                                                                     ->
                                                                    match 
                                                                    (uu____13325,
                                                                    uu____13326)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13437
                                                                    =
                                                                    let uu____13445
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13445
                                                                     in
                                                                    (match uu____13437
                                                                    with
                                                                    | 
                                                                    (uu____13459,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13470
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13470
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13475
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13475
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
                                                                 uu____13268
                                                                in
                                                             (match uu____13254
                                                              with
                                                              | (uu____13496,arg_vars,elim_eqns_or_guards,uu____13499)
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
                                                                  let dapp1 =
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
                                                                    let uu____13526
                                                                    =
                                                                    let uu____13534
                                                                    =
                                                                    let uu____13535
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13536
                                                                    =
                                                                    let uu____13547
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13549
                                                                    =
                                                                    let uu____13550
                                                                    =
                                                                    let uu____13555
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13555)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13550
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13547,
                                                                    uu____13549)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13535
                                                                    uu____13536
                                                                     in
                                                                    (uu____13534,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13526
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13570
                                                                    =
                                                                    let uu____13576
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13576,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13570
                                                                     in
                                                                    let uu____13579
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13579
                                                                    then
                                                                    let x =
                                                                    let uu____13588
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13588,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13593
                                                                    =
                                                                    let uu____13601
                                                                    =
                                                                    let uu____13602
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13603
                                                                    =
                                                                    let uu____13614
                                                                    =
                                                                    let uu____13619
                                                                    =
                                                                    let uu____13622
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13622]
                                                                     in
                                                                    [uu____13619]
                                                                     in
                                                                    let uu____13627
                                                                    =
                                                                    let uu____13628
                                                                    =
                                                                    let uu____13633
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13635
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13633,
                                                                    uu____13635)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13628
                                                                     in
                                                                    (uu____13614,
                                                                    [x],
                                                                    uu____13627)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13602
                                                                    uu____13603
                                                                     in
                                                                    let uu____13650
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13601,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13650)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13593
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13661
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
                                                                    (let uu____13699
                                                                    =
                                                                    let uu____13700
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____13700
                                                                    dapp1  in
                                                                    [uu____13699])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13661
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____13707
                                                                    =
                                                                    let uu____13715
                                                                    =
                                                                    let uu____13716
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13717
                                                                    =
                                                                    let uu____13728
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13730
                                                                    =
                                                                    let uu____13731
                                                                    =
                                                                    let uu____13736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____13736)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13731
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13728,
                                                                    uu____13730)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13716
                                                                    uu____13717
                                                                     in
                                                                    (uu____13715,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13707)
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
                                                        let uu____13755 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_args
                                                            args env'
                                                           in
                                                        (match uu____13755
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
                                                                 | uu____13809
                                                                    ->
                                                                    let uu____13810
                                                                    =
                                                                    let uu____13816
                                                                    =
                                                                    let uu____13818
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13818
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13816)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13810
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13838
                                                                    =
                                                                    let uu____13840
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13840
                                                                     in
                                                                    if
                                                                    uu____13838
                                                                    then
                                                                    let uu____13856
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13856]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____13859
                                                               =
                                                               let uu____13873
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____13930
                                                                     ->
                                                                    fun
                                                                    uu____13931
                                                                     ->
                                                                    match 
                                                                    (uu____13930,
                                                                    uu____13931)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14042
                                                                    =
                                                                    let uu____14050
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14050
                                                                     in
                                                                    (match uu____14042
                                                                    with
                                                                    | 
                                                                    (uu____14064,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14075
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14075
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14080
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14080
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
                                                                 uu____13873
                                                                in
                                                             (match uu____13859
                                                              with
                                                              | (uu____14101,arg_vars,elim_eqns_or_guards,uu____14104)
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
                                                                  let dapp1 =
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
                                                                    let uu____14131
                                                                    =
                                                                    let uu____14139
                                                                    =
                                                                    let uu____14140
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14141
                                                                    =
                                                                    let uu____14152
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14154
                                                                    =
                                                                    let uu____14155
                                                                    =
                                                                    let uu____14160
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14160)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14155
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14152,
                                                                    uu____14154)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14140
                                                                    uu____14141
                                                                     in
                                                                    (uu____14139,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14131
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14175
                                                                    =
                                                                    let uu____14181
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14181,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14175
                                                                     in
                                                                    let uu____14184
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14184
                                                                    then
                                                                    let x =
                                                                    let uu____14193
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14193,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14198
                                                                    =
                                                                    let uu____14206
                                                                    =
                                                                    let uu____14207
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14208
                                                                    =
                                                                    let uu____14219
                                                                    =
                                                                    let uu____14224
                                                                    =
                                                                    let uu____14227
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14227]
                                                                     in
                                                                    [uu____14224]
                                                                     in
                                                                    let uu____14232
                                                                    =
                                                                    let uu____14233
                                                                    =
                                                                    let uu____14238
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14238,
                                                                    uu____14240)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14233
                                                                     in
                                                                    (uu____14219,
                                                                    [x],
                                                                    uu____14232)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14207
                                                                    uu____14208
                                                                     in
                                                                    let uu____14255
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14206,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14198
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14266
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
                                                                    (let uu____14304
                                                                    =
                                                                    let uu____14305
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14305
                                                                    dapp1  in
                                                                    [uu____14304])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14266
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14312
                                                                    =
                                                                    let uu____14320
                                                                    =
                                                                    let uu____14321
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14322
                                                                    =
                                                                    let uu____14333
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14335
                                                                    =
                                                                    let uu____14336
                                                                    =
                                                                    let uu____14341
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14341)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14336
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14333,
                                                                    uu____14335)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14321
                                                                    uu____14322
                                                                     in
                                                                    (uu____14320,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14312)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14358 ->
                                                        ((let uu____14360 =
                                                            let uu____14366 =
                                                              let uu____14368
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____14370
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____14368
                                                                uu____14370
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____14366)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14360);
                                                         ([], [])))
                                                in
                                             let uu____14378 = encode_elim ()
                                                in
                                             (match uu____14378 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14404 =
                                                      let uu____14407 =
                                                        let uu____14410 =
                                                          let uu____14413 =
                                                            let uu____14416 =
                                                              let uu____14417
                                                                =
                                                                let uu____14429
                                                                  =
                                                                  let uu____14430
                                                                    =
                                                                    let uu____14432
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14432
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____14430
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14429)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14417
                                                               in
                                                            [uu____14416]  in
                                                          let uu____14439 =
                                                            let uu____14442 =
                                                              let uu____14445
                                                                =
                                                                let uu____14448
                                                                  =
                                                                  let uu____14451
                                                                    =
                                                                    let uu____14454
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14459
                                                                    =
                                                                    let uu____14462
                                                                    =
                                                                    let uu____14463
                                                                    =
                                                                    let uu____14471
                                                                    =
                                                                    let uu____14472
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14473
                                                                    =
                                                                    let uu____14484
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14484)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14472
                                                                    uu____14473
                                                                     in
                                                                    (uu____14471,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14463
                                                                     in
                                                                    let uu____14497
                                                                    =
                                                                    let uu____14500
                                                                    =
                                                                    let uu____14501
                                                                    =
                                                                    let uu____14509
                                                                    =
                                                                    let uu____14510
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14511
                                                                    =
                                                                    let uu____14522
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14524
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14522,
                                                                    uu____14524)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14510
                                                                    uu____14511
                                                                     in
                                                                    (uu____14509,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14501
                                                                     in
                                                                    [uu____14500]
                                                                     in
                                                                    uu____14462
                                                                    ::
                                                                    uu____14497
                                                                     in
                                                                    uu____14454
                                                                    ::
                                                                    uu____14459
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14451
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14448
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14445
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14442
                                                             in
                                                          FStar_List.append
                                                            uu____14413
                                                            uu____14439
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14410
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14407
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14404
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14562  ->
              fun se  ->
                match uu____14562 with
                | (g,env1) ->
                    let uu____14582 = encode_sigelt env1 se  in
                    (match uu____14582 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14650 =
        match uu____14650 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____14687 ->
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
                 ((let uu____14695 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14695
                   then
                     let uu____14700 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14702 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14704 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14700 uu____14702 uu____14704
                   else ());
                  (let uu____14709 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____14709 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14727 =
                         let uu____14735 =
                           let uu____14737 =
                             let uu____14739 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____14739
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____14737  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____14735
                          in
                       (match uu____14727 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____14759 = FStar_Options.log_queries ()
                                 in
                              if uu____14759
                              then
                                let uu____14762 =
                                  let uu____14764 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14766 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14768 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14764 uu____14766 uu____14768
                                   in
                                FStar_Pervasives_Native.Some uu____14762
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____14792,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____14812 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____14812 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____14839 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____14839 with | (uu____14866,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____14882 'Auu____14883 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____14882 *
      'Auu____14883) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____14956  ->
              match uu____14956 with
              | (l,uu____14969,uu____14970) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15021  ->
              match uu____15021 with
              | (l,uu____15036,uu____15037) ->
                  let uu____15048 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____15051 =
                    let uu____15054 =
                      let uu____15055 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15055  in
                    [uu____15054]  in
                  uu____15048 :: uu____15051))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15084 =
      let uu____15087 =
        let uu____15088 = FStar_Util.psmap_empty ()  in
        let uu____15103 = FStar_Util.psmap_empty ()  in
        let uu____15106 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15110 =
          let uu____15112 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15112 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15088;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15103;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____15106;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15110;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____15087]  in
    FStar_ST.op_Colon_Equals last_env uu____15084
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15154 = FStar_ST.op_Bang last_env  in
      match uu____15154 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15182 ->
          let uu___397_15185 = e  in
          let uu____15186 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___397_15185.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___397_15185.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___397_15185.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___397_15185.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___397_15185.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___397_15185.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___397_15185.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___397_15185.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15186;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___397_15185.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15194 = FStar_ST.op_Bang last_env  in
    match uu____15194 with
    | [] -> failwith "Empty env stack"
    | uu____15221::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15253  ->
    let uu____15254 = FStar_ST.op_Bang last_env  in
    match uu____15254 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15314  ->
    let uu____15315 = FStar_ST.op_Bang last_env  in
    match uu____15315 with
    | [] -> failwith "Popping an empty stack"
    | uu____15342::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15379  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15432  ->
         let uu____15433 = snapshot_env ()  in
         match uu____15433 with
         | (env_depth,()) ->
             let uu____15455 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____15455 with
              | (varops_depth,()) ->
                  let uu____15477 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____15477 with
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
        (fun uu____15535  ->
           let uu____15536 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____15536 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____15631 = snapshot msg  in () 
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
        | (uu____15677::uu____15678,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___398_15686 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___398_15686.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___398_15686.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___398_15686.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15687 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____15707 =
        let uu____15710 =
          let uu____15711 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____15711  in
        let uu____15712 = open_fact_db_tags env  in uu____15710 ::
          uu____15712
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15707
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____15739 = encode_sigelt env se  in
      match uu____15739 with
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
        let uu____15784 = FStar_Options.log_queries ()  in
        if uu____15784
        then
          let uu____15789 =
            let uu____15790 =
              let uu____15792 =
                let uu____15794 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15794 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15792  in
            FStar_SMTEncoding_Term.Caption uu____15790  in
          uu____15789 :: decls
        else decls  in
      (let uu____15813 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____15813
       then
         let uu____15816 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____15816
       else ());
      (let env =
         let uu____15822 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____15822 tcenv  in
       let uu____15823 = encode_top_level_facts env se  in
       match uu____15823 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____15837 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____15837)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____15851 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____15851
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____15866 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____15866
          then
            let uu____15869 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____15869
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____15915  ->
                    fun se  ->
                      match uu____15915 with
                      | (g,env2) ->
                          let uu____15935 = encode_top_level_facts env2 se
                             in
                          (match uu____15935 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____15958 =
            encode_signature
              (let uu___399_15967 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___399_15967.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___399_15967.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___399_15967.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___399_15967.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___399_15967.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___399_15967.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___399_15967.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___399_15967.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___399_15967.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___399_15967.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____15958 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____15987 = FStar_Options.log_queries ()  in
                if uu____15987
                then
                  let msg = Prims.strcat "Externals for " name  in
                  [FStar_SMTEncoding_Term.Module
                     (name,
                       (FStar_List.append
                          ((FStar_SMTEncoding_Term.Caption msg) :: decls1)
                          [FStar_SMTEncoding_Term.Caption
                             (Prims.strcat "End " msg)]))]
                else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
              (set_env
                 (let uu___400_16007 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___400_16007.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___400_16007.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___400_16007.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___400_16007.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___400_16007.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___400_16007.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___400_16007.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___400_16007.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___400_16007.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___400_16007.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____16010 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16010
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let decls1 = caption decls  in
                FStar_SMTEncoding_Z3.giveZ3 decls1))))
  
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
        (let uu____16075 =
           let uu____16077 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16077.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16075);
        (let env =
           let uu____16079 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16079 tcenv  in
         let uu____16080 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16119 = aux rest  in
                 (match uu____16119 with
                  | (out,rest1) ->
                      let t =
                        let uu____16147 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16147 with
                        | FStar_Pervasives_Native.Some uu____16150 ->
                            let uu____16151 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16151
                              x.FStar_Syntax_Syntax.sort
                        | uu____16152 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16156 =
                        let uu____16159 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___401_16162 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___401_16162.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___401_16162.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16159 :: out  in
                      (uu____16156, rest1))
             | uu____16167 -> ([], bindings)  in
           let uu____16174 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16174 with
           | (closing,bindings) ->
               let uu____16201 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16201, bindings)
            in
         match uu____16080 with
         | (q1,bindings) ->
             let uu____16232 = encode_env_bindings env bindings  in
             (match uu____16232 with
              | (env_decls,env1) ->
                  ((let uu____16254 =
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
                    if uu____16254
                    then
                      let uu____16261 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16261
                    else ());
                   (let uu____16266 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16266 with
                    | (phi,qdecls) ->
                        let uu____16287 =
                          let uu____16292 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16292 phi
                           in
                        (match uu____16287 with
                         | (labels,phi1) ->
                             let uu____16309 = encode_labels labels  in
                             (match uu____16309 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____16346 =
                                      FStar_Options.log_queries ()  in
                                    if uu____16346
                                    then
                                      let uu____16351 =
                                        let uu____16352 =
                                          let uu____16354 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____16354
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____16352
                                         in
                                      [uu____16351]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____16363 =
                                      let uu____16371 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16372 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____16371,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16372)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16363
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
  