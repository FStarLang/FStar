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
        (Prims.string,FStar_SMTEncoding_Term.sort)
          FStar_Pervasives_Native.tuple2 Prims.list ->
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
                                  (let uu___382_5432 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___382_5432.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___382_5432.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___382_5432.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___382_5432.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___382_5432.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___382_5432.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___382_5432.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___382_5432.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___382_5432.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___382_5432.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___382_5432.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___382_5432.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___382_5432.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___382_5432.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___382_5432.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___382_5432.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___382_5432.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___382_5432.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___382_5432.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___382_5432.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___382_5432.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___382_5432.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___382_5432.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___382_5432.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___382_5432.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___382_5432.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___382_5432.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___382_5432.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___382_5432.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___382_5432.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___382_5432.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___382_5432.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___382_5432.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___382_5432.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___382_5432.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___382_5432.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___382_5432.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___382_5432.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___382_5432.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___382_5432.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___382_5432.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___382_5432.FStar_TypeChecker_Env.nbe)
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
                        let arity = FStar_List.length formals  in
                        let uu____5536 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____5536 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____5570 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___372_5631  ->
                                       match uu___372_5631 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____5635 =
                                             FStar_Util.prefix vars  in
                                           (match uu____5635 with
                                            | (uu____5659,(xxsym,uu____5661))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____5685 =
                                                  let uu____5686 =
                                                    let uu____5694 =
                                                      let uu____5695 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5696 =
                                                        let uu____5707 =
                                                          let uu____5708 =
                                                            let uu____5713 =
                                                              let uu____5714
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____5714
                                                               in
                                                            (vapp,
                                                              uu____5713)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____5708
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5707)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5695 uu____5696
                                                       in
                                                    (uu____5694,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5686
                                                   in
                                                [uu____5685])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____5729 =
                                             FStar_Util.prefix vars  in
                                           (match uu____5729 with
                                            | (uu____5753,(xxsym,uu____5755))
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
                                                let uu____5787 =
                                                  let uu____5788 =
                                                    let uu____5796 =
                                                      let uu____5797 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5798 =
                                                        let uu____5809 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5809)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5797 uu____5798
                                                       in
                                                    (uu____5796,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5788
                                                   in
                                                [uu____5787])
                                       | uu____5822 -> []))
                                in
                             let uu____5823 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5823 with
                              | (vars,guards,env',decls1,uu____5850) ->
                                  let uu____5863 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5876 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5876, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5880 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5880 with
                                         | (g,ds) ->
                                             let uu____5893 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5893,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5863 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5910 =
                                           let uu____5918 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5918)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5910
                                          in
                                       let uu____5924 =
                                         let vname_decl =
                                           let uu____5932 =
                                             let uu____5944 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5964  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5944,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5932
                                            in
                                         let uu____5975 =
                                           let env2 =
                                             let uu___383_5981 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___383_5981.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____5982 =
                                             let uu____5984 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5984  in
                                           if uu____5982
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5975 with
                                         | (tok_typing,decls2) ->
                                             let uu____6001 =
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
                                                   let uu____6025 =
                                                     let uu____6026 =
                                                       let uu____6029 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6029
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6026
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6025)
                                               | uu____6039 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6054 =
                                                       let uu____6062 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6062]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6054
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6084 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6085 =
                                                       let uu____6096 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6096)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6084 uu____6085
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6106 =
                                                       let uu____6114 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6114,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6106
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
                                                       let uu____6153 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6154 =
                                                         let uu____6165 =
                                                           let uu____6166 =
                                                             let uu____6171 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6172 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6171,
                                                               uu____6172)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6166
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6165)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6153
                                                         uu____6154
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
                                             (match uu____6001 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5924 with
                                        | (decls2,env2) ->
                                            let uu____6223 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____6233 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____6233 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____6248 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____6248,
                                                    decls)
                                               in
                                            (match uu____6223 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____6265 =
                                                     let uu____6273 =
                                                       let uu____6274 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6275 =
                                                         let uu____6286 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____6286)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6274
                                                         uu____6275
                                                        in
                                                     (uu____6273,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____6265
                                                    in
                                                 let freshness =
                                                   let uu____6302 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____6302
                                                   then
                                                     let uu____6310 =
                                                       let uu____6311 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6312 =
                                                         let uu____6325 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____6343 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____6325,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____6343)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____6311
                                                         uu____6312
                                                        in
                                                     let uu____6349 =
                                                       let uu____6352 =
                                                         let uu____6353 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____6353 env2
                                                           vapp vars
                                                          in
                                                       [uu____6352]  in
                                                     uu____6310 :: uu____6349
                                                   else []  in
                                                 let g =
                                                   let uu____6359 =
                                                     let uu____6362 =
                                                       let uu____6365 =
                                                         let uu____6368 =
                                                           let uu____6371 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____6371
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____6368
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____6365
                                                        in
                                                     FStar_List.append decls2
                                                       uu____6362
                                                      in
                                                   FStar_List.append decls11
                                                     uu____6359
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
          let uu____6413 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6413 with
          | FStar_Pervasives_Native.None  ->
              let uu____6424 = encode_free_var false env x t t_norm []  in
              (match uu____6424 with
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
            let uu____6495 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6495 with
            | (decls,env1) ->
                let uu____6514 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6514
                then
                  let uu____6523 =
                    let uu____6526 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6526  in
                  (uu____6523, env1)
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
             (fun uu____6586  ->
                fun lb  ->
                  match uu____6586 with
                  | (decls,env1) ->
                      let uu____6606 =
                        let uu____6613 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____6613
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____6606 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____6646 = FStar_Syntax_Util.head_and_args t  in
    match uu____6646 with
    | (hd1,args) ->
        let uu____6690 =
          let uu____6691 = FStar_Syntax_Util.un_uinst hd1  in
          uu____6691.FStar_Syntax_Syntax.n  in
        (match uu____6690 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____6697,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____6721 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____6732 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___384_6740 = en  in
    let uu____6741 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___384_6740.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___384_6740.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___384_6740.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___384_6740.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___384_6740.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____6741;
      FStar_SMTEncoding_Env.nolabels =
        (uu___384_6740.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___384_6740.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___384_6740.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___384_6740.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___384_6740.FStar_SMTEncoding_Env.encoding_quantifier)
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
    fun uu____6773  ->
      fun quals  ->
        match uu____6773 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____6880 = FStar_Util.first_N nbinders formals  in
              match uu____6880 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6981  ->
                         fun uu____6982  ->
                           match (uu____6981, uu____6982) with
                           | ((formal,uu____7008),(binder,uu____7010)) ->
                               let uu____7031 =
                                 let uu____7038 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7038)  in
                               FStar_Syntax_Syntax.NT uu____7031) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7052 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7093  ->
                              match uu____7093 with
                              | (x,i) ->
                                  let uu____7112 =
                                    let uu___385_7113 = x  in
                                    let uu____7114 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___385_7113.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___385_7113.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7114
                                    }  in
                                  (uu____7112, i)))
                       in
                    FStar_All.pipe_right uu____7052
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7138 =
                      let uu____7143 = FStar_Syntax_Subst.compress body  in
                      let uu____7144 =
                        let uu____7145 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7145
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7143 uu____7144
                       in
                    uu____7138 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____7230 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____7230
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___386_7237 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___386_7237.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___386_7237.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___386_7237.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___386_7237.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___386_7237.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___386_7237.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___386_7237.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___386_7237.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___386_7237.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___386_7237.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___386_7237.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___386_7237.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___386_7237.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___386_7237.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___386_7237.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___386_7237.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___386_7237.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___386_7237.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___386_7237.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___386_7237.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___386_7237.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___386_7237.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___386_7237.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___386_7237.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___386_7237.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___386_7237.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___386_7237.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___386_7237.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___386_7237.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___386_7237.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___386_7237.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___386_7237.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___386_7237.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___386_7237.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___386_7237.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___386_7237.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___386_7237.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___386_7237.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___386_7237.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___386_7237.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___386_7237.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___386_7237.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____7287 = FStar_Syntax_Util.abs_formals e  in
                match uu____7287 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____7369::uu____7370 ->
                         let uu____7391 =
                           let uu____7392 =
                             let uu____7395 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____7395
                              in
                           uu____7392.FStar_Syntax_Syntax.n  in
                         (match uu____7391 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____7453 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____7453 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____7510 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____7510
                                   then
                                     let uu____7556 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____7556 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____7677  ->
                                                   fun uu____7678  ->
                                                     match (uu____7677,
                                                             uu____7678)
                                                     with
                                                     | ((x,uu____7704),
                                                        (b,uu____7706)) ->
                                                         let uu____7727 =
                                                           let uu____7734 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____7734)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____7727)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____7742 =
                                            let uu____7771 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____7771)  in
                                          (uu____7742, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____7870 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____7870 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8043) ->
                              let uu____8048 =
                                let uu____8077 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8077  in
                              (uu____8048, true)
                          | uu____8170 when Prims.op_Negation norm1 ->
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
                          | uu____8173 ->
                              let uu____8174 =
                                let uu____8176 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____8178 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____8176 uu____8178
                                 in
                              failwith uu____8174)
                     | uu____8214 ->
                         let rec aux' t_norm2 =
                           let uu____8254 =
                             let uu____8255 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____8255.FStar_Syntax_Syntax.n  in
                           match uu____8254 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____8313 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____8313 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____8356 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____8356 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____8483) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____8488 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___388_8560  ->
                  match () with
                  | () ->
                      let uu____8567 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8567
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8583 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8646  ->
                                   fun lb  ->
                                     match uu____8646 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8701 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8701
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8707 =
                                             let uu____8716 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8716
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8707 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8583 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____8846 =
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
                               | uu____8859 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8869 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____8869 vars)
                                   else
                                     (let uu____8872 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____8872)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____8933;
                                    FStar_Syntax_Syntax.lbeff = uu____8934;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8936;
                                    FStar_Syntax_Syntax.lbpos = uu____8937;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8961 =
                                     let uu____8970 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8970 with
                                     | (tcenv',uu____8988,e_t) ->
                                         let uu____8994 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9011 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8994 with
                                          | (e1,t_norm1) ->
                                              ((let uu___389_9038 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___389_9038.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8961 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9052 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9052 with
                                         | ((binders,body,uu____9074,t_body),curry)
                                             ->
                                             ((let uu____9088 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9088
                                               then
                                                 let uu____9093 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9096 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9093 uu____9096
                                               else ());
                                              (let uu____9101 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9101 with
                                               | (vars,guards,env'1,binder_decls,uu____9128)
                                                   ->
                                                   let body1 =
                                                     let uu____9142 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9142
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
                                                     let uu____9166 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____9166 curry
                                                       fvb vars
                                                      in
                                                   let uu____9167 =
                                                     let is_logical =
                                                       let uu____9180 =
                                                         let uu____9181 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____9181.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____9180 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____9187 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____9191 =
                                                         let uu____9192 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____9192
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____9191
                                                         (fun lid  ->
                                                            let uu____9201 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____9201
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____9202 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____9202
                                                     then
                                                       let uu____9218 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____9219 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____9218,
                                                         uu____9219)
                                                     else
                                                       (let uu____9230 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____9230))
                                                      in
                                                   (match uu____9167 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____9254 =
                                                            let uu____9262 =
                                                              let uu____9263
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____9264
                                                                =
                                                                let uu____9275
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____9275)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____9263
                                                                uu____9264
                                                               in
                                                            let uu____9284 =
                                                              let uu____9285
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____9285
                                                               in
                                                            (uu____9262,
                                                              uu____9284,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____9254
                                                           in
                                                        let uu____9291 =
                                                          let uu____9294 =
                                                            let uu____9297 =
                                                              let uu____9300
                                                                =
                                                                let uu____9303
                                                                  =
                                                                  primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1
                                                                   in
                                                                FStar_List.append
                                                                  [eqn]
                                                                  uu____9303
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____9300
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____9297
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____9294
                                                           in
                                                        (uu____9291, env2))))))
                               | uu____9308 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9373 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____9373,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9379 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9432  ->
                                         fun fvb  ->
                                           match uu____9432 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9487 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9487
                                                  in
                                               let gtok =
                                                 let uu____9491 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9491
                                                  in
                                               let env4 =
                                                 let uu____9494 =
                                                   let uu____9497 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9497
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9494
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9379 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9624
                                     t_norm uu____9626 =
                                     match (uu____9624, uu____9626) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9658;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9659;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9661;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9662;_})
                                         ->
                                         let uu____9689 =
                                           let uu____9698 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9698 with
                                           | (tcenv',uu____9716,e_t) ->
                                               let uu____9722 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9739 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9722 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___390_9766 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___390_9766.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9689 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9785 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9785
                                                then
                                                  let uu____9790 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9792 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9794 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9790 uu____9792
                                                    uu____9794
                                                else ());
                                               (let uu____9799 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____9799 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____9839 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____9839
                                                      then
                                                        let uu____9844 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____9847 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____9849 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____9852 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____9844
                                                          uu____9847
                                                          uu____9849
                                                          uu____9852
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____9862 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____9862 with
                                                      | (vars,guards,env'1,binder_decls,uu____9893)
                                                          ->
                                                          let decl_g =
                                                            let uu____9907 =
                                                              let uu____9919
                                                                =
                                                                let uu____9922
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____9922
                                                                 in
                                                              (g, uu____9919,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____9907
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
                                                            let uu____9942 =
                                                              let uu____9950
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____9950)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____9942
                                                             in
                                                          let gsapp =
                                                            let uu____9957 =
                                                              let uu____9965
                                                                =
                                                                let uu____9968
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____9968 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____9965)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____9957
                                                             in
                                                          let gmax =
                                                            let uu____9977 =
                                                              let uu____9985
                                                                =
                                                                let uu____9988
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____9988 ::
                                                                  vars_tm
                                                                 in
                                                              (g, uu____9985)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____9977
                                                             in
                                                          let body1 =
                                                            let uu____9997 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____9997
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10002 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10002
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10020
                                                                   =
                                                                   let uu____10028
                                                                    =
                                                                    let uu____10029
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10030
                                                                    =
                                                                    let uu____10046
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
                                                                    uu____10046)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10029
                                                                    uu____10030
                                                                     in
                                                                   let uu____10060
                                                                    =
                                                                    let uu____10061
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10061
                                                                     in
                                                                   (uu____10028,
                                                                    uu____10060,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10020
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10068
                                                                   =
                                                                   let uu____10076
                                                                    =
                                                                    let uu____10077
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10078
                                                                    =
                                                                    let uu____10089
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10089)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10077
                                                                    uu____10078
                                                                     in
                                                                   (uu____10076,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10068
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10103
                                                                   =
                                                                   let uu____10111
                                                                    =
                                                                    let uu____10112
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10113
                                                                    =
                                                                    let uu____10124
                                                                    =
                                                                    let uu____10125
                                                                    =
                                                                    let uu____10130
                                                                    =
                                                                    let uu____10131
                                                                    =
                                                                    let uu____10139
                                                                    =
                                                                    let uu____10142
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10142
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10139)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10131
                                                                     in
                                                                    (gsapp,
                                                                    uu____10130)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10125
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10124)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10112
                                                                    uu____10113
                                                                     in
                                                                   (uu____10111,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10103
                                                                  in
                                                               let uu____10159
                                                                 =
                                                                 let uu____10168
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____10168
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____10197)
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
                                                                    let uu____10219
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10219
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____10221
                                                                    =
                                                                    let uu____10229
                                                                    =
                                                                    let uu____10230
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10231
                                                                    =
                                                                    let uu____10242
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10242)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10230
                                                                    uu____10231
                                                                     in
                                                                    (uu____10229,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10221
                                                                     in
                                                                    let uu____10255
                                                                    =
                                                                    let uu____10264
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____10264
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10279
                                                                    =
                                                                    let uu____10282
                                                                    =
                                                                    let uu____10283
                                                                    =
                                                                    let uu____10291
                                                                    =
                                                                    let uu____10292
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10293
                                                                    =
                                                                    let uu____10304
                                                                    =
                                                                    let uu____10305
                                                                    =
                                                                    let uu____10310
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____10310,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____10305
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10304)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10292
                                                                    uu____10293
                                                                     in
                                                                    (uu____10291,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10283
                                                                     in
                                                                    [uu____10282]
                                                                     in
                                                                    (d3,
                                                                    uu____10279)
                                                                     in
                                                                    (match uu____10255
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
                                                               (match uu____10159
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
                                   let uu____10373 =
                                     let uu____10386 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10449  ->
                                          fun uu____10450  ->
                                            match (uu____10449, uu____10450)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____10575 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____10575 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10386
                                      in
                                   (match uu____10373 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10648 =
                                          let isDeclFun uu___373_10663 =
                                            match uu___373_10663 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10665 -> true
                                            | uu____10678 -> false  in
                                          let uu____10680 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10680
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____10648 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10720 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___374_10726  ->
                                        match uu___374_10726 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10729 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10737 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10737)))
                                in
                             if uu____10720
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___392_10759  ->
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
                   let uu____10797 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10797
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
        let uu____10867 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10867 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10873 = encode_sigelt' env se  in
      match uu____10873 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10885 =
                  let uu____10886 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____10886  in
                [uu____10885]
            | uu____10889 ->
                let uu____10890 =
                  let uu____10893 =
                    let uu____10894 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10894  in
                  uu____10893 :: g  in
                let uu____10897 =
                  let uu____10900 =
                    let uu____10901 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____10901  in
                  [uu____10900]  in
                FStar_List.append uu____10890 uu____10897
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
        let uu____10917 =
          let uu____10918 = FStar_Syntax_Subst.compress t  in
          uu____10918.FStar_Syntax_Syntax.n  in
        match uu____10917 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10923)) -> s = "opaque_to_smt"
        | uu____10928 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____10937 =
          let uu____10938 = FStar_Syntax_Subst.compress t  in
          uu____10938.FStar_Syntax_Syntax.n  in
        match uu____10937 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10943)) -> s = "uninterpreted_by_smt"
        | uu____10948 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10954 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____10960 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____10972 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____10973 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10974 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10987 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10989 =
            let uu____10991 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____10991  in
          if uu____10989
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11020 ->
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
               let uu____11052 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11052 with
               | (formals,uu____11072) ->
                   let arity = FStar_List.length formals  in
                   let uu____11096 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11096 with
                    | (aname,atok,env2) ->
                        let uu____11122 =
                          let uu____11127 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11127 env2
                           in
                        (match uu____11122 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11139 =
                                 let uu____11140 =
                                   let uu____11152 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____11172  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11152,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11140
                                  in
                               [uu____11139;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____11189 =
                               let aux uu____11250 uu____11251 =
                                 match (uu____11250, uu____11251) with
                                 | ((bv,uu____11310),(env3,acc_sorts,acc)) ->
                                     let uu____11357 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____11357 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____11189 with
                              | (uu____11441,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____11467 =
                                      let uu____11475 =
                                        let uu____11476 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11477 =
                                          let uu____11488 =
                                            let uu____11489 =
                                              let uu____11494 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____11494)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____11489
                                             in
                                          ([[app]], xs_sorts, uu____11488)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11476 uu____11477
                                         in
                                      (uu____11475,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11467
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
                                    let uu____11511 =
                                      let uu____11519 =
                                        let uu____11520 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11521 =
                                          let uu____11532 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____11532)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11520 uu____11521
                                         in
                                      (uu____11519,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11511
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____11547 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____11547 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11573,uu____11574)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____11575 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____11575 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11597,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____11604 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___375_11610  ->
                      match uu___375_11610 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____11613 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____11619 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11622 -> false))
               in
            Prims.op_Negation uu____11604  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____11632 =
               let uu____11639 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____11639 env fv t quals  in
             match uu____11632 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____11658 =
                   let uu____11659 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____11659  in
                 (uu____11658, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____11665 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____11665 with
           | (uvs,f1) ->
               let env1 =
                 let uu___393_11677 = env  in
                 let uu____11678 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___393_11677.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___393_11677.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___393_11677.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____11678;
                   FStar_SMTEncoding_Env.warn =
                     (uu___393_11677.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___393_11677.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___393_11677.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___393_11677.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___393_11677.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___393_11677.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___393_11677.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____11680 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____11680 with
                | (f3,decls) ->
                    let g =
                      let uu____11694 =
                        let uu____11695 =
                          let uu____11703 =
                            let uu____11704 =
                              let uu____11706 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____11706
                               in
                            FStar_Pervasives_Native.Some uu____11704  in
                          let uu____11710 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____11703, uu____11710)  in
                        FStar_SMTEncoding_Util.mkAssume uu____11695  in
                      [uu____11694]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____11715) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____11729 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____11751 =
                       let uu____11754 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____11754.FStar_Syntax_Syntax.fv_name  in
                     uu____11751.FStar_Syntax_Syntax.v  in
                   let uu____11755 =
                     let uu____11757 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____11757  in
                   if uu____11755
                   then
                     let val_decl =
                       let uu___394_11789 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___394_11789.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___394_11789.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___394_11789.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____11790 = encode_sigelt' env1 val_decl  in
                     match uu____11790 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____11729 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____11826,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____11828;
                          FStar_Syntax_Syntax.lbtyp = uu____11829;
                          FStar_Syntax_Syntax.lbeff = uu____11830;
                          FStar_Syntax_Syntax.lbdef = uu____11831;
                          FStar_Syntax_Syntax.lbattrs = uu____11832;
                          FStar_Syntax_Syntax.lbpos = uu____11833;_}::[]),uu____11834)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____11853 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____11853 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____11896 =
                   let uu____11899 =
                     let uu____11900 =
                       let uu____11908 =
                         let uu____11909 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____11910 =
                           let uu____11921 =
                             let uu____11922 =
                               let uu____11927 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____11927)  in
                             FStar_SMTEncoding_Util.mkEq uu____11922  in
                           ([[b2t_x]], [xx], uu____11921)  in
                         FStar_SMTEncoding_Term.mkForall uu____11909
                           uu____11910
                          in
                       (uu____11908,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11900  in
                   [uu____11899]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____11896
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____11959,uu____11960) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___376_11970  ->
                  match uu___376_11970 with
                  | FStar_Syntax_Syntax.Discriminator uu____11972 -> true
                  | uu____11974 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____11976,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____11988 =
                     let uu____11990 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____11990.FStar_Ident.idText  in
                   uu____11988 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___377_11997  ->
                     match uu___377_11997 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12000 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12003) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___378_12017  ->
                  match uu___378_12017 with
                  | FStar_Syntax_Syntax.Projector uu____12019 -> true
                  | uu____12025 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12029 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12029 with
           | FStar_Pervasives_Native.Some uu____12036 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___395_12038 = se  in
                 let uu____12039 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12039;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___395_12038.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___395_12038.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___395_12038.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12042) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12057) ->
          let uu____12066 = encode_sigelts env ses  in
          (match uu____12066 with
           | (g,env1) ->
               let uu____12083 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___379_12106  ->
                         match uu___379_12106 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12108;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12109;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12110;_}
                             -> false
                         | uu____12117 -> true))
                  in
               (match uu____12083 with
                | (g',inversions) ->
                    let uu____12133 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___380_12154  ->
                              match uu___380_12154 with
                              | FStar_SMTEncoding_Term.DeclFun uu____12156 ->
                                  true
                              | uu____12169 -> false))
                       in
                    (match uu____12133 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12186,tps,k,uu____12189,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___381_12208  ->
                    match uu___381_12208 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12212 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____12225 = c  in
              match uu____12225 with
              | (name,args,uu____12230,uu____12231,uu____12232) ->
                  let uu____12243 =
                    let uu____12244 =
                      let uu____12256 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____12283  ->
                                match uu____12283 with
                                | (uu____12292,sort,uu____12294) -> sort))
                         in
                      (name, uu____12256, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12244  in
                  [uu____12243]
            else
              (let uu____12305 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____12305 c)
             in
          let inversion_axioms tapp vars =
            let uu____12333 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____12341 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____12341 FStar_Option.isNone))
               in
            if uu____12333
            then []
            else
              (let uu____12376 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____12376 with
               | (xxsym,xx) ->
                   let uu____12389 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____12428  ->
                             fun l  ->
                               match uu____12428 with
                               | (out,decls) ->
                                   let uu____12448 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____12448 with
                                    | (uu____12459,data_t) ->
                                        let uu____12461 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____12461 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____12505 =
                                                 let uu____12506 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____12506.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____12505 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____12509,indices) ->
                                                   indices
                                               | uu____12535 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____12565  ->
                                                         match uu____12565
                                                         with
                                                         | (x,uu____12573) ->
                                                             let uu____12578
                                                               =
                                                               let uu____12579
                                                                 =
                                                                 let uu____12587
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____12587,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____12579
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____12578)
                                                    env)
                                                in
                                             let uu____12592 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____12592 with
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
                                                      let uu____12622 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____12640
                                                                 =
                                                                 let uu____12645
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____12645,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____12640)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____12622
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____12648 =
                                                      let uu____12649 =
                                                        let uu____12654 =
                                                          let uu____12655 =
                                                            let uu____12660 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____12660,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____12655
                                                           in
                                                        (out, uu____12654)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____12649
                                                       in
                                                    (uu____12648,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____12389 with
                    | (data_ax,decls) ->
                        let uu____12673 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____12673 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____12690 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____12690 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____12697 =
                                 let uu____12705 =
                                   let uu____12706 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____12707 =
                                     let uu____12718 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____12731 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____12718,
                                       uu____12731)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____12706 uu____12707
                                    in
                                 let uu____12740 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____12705,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____12740)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____12697
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____12746 =
            let uu____12751 =
              let uu____12752 = FStar_Syntax_Subst.compress k  in
              uu____12752.FStar_Syntax_Syntax.n  in
            match uu____12751 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____12787 -> (tps, k)  in
          (match uu____12746 with
           | (formals,res) ->
               let uu____12794 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____12794 with
                | (formals1,res1) ->
                    let uu____12805 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____12805 with
                     | (vars,guards,env',binder_decls,uu____12830) ->
                         let arity = FStar_List.length vars  in
                         let uu____12844 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____12844 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____12874 =
                                  let uu____12882 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____12882)  in
                                FStar_SMTEncoding_Util.mkApp uu____12874  in
                              let uu____12888 =
                                let tname_decl =
                                  let uu____12898 =
                                    let uu____12899 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____12927  ->
                                              match uu____12927 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____12948 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____12899,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____12948, false)
                                     in
                                  constructor_or_logic_type_decl uu____12898
                                   in
                                let uu____12956 =
                                  match vars with
                                  | [] ->
                                      let uu____12969 =
                                        let uu____12970 =
                                          let uu____12973 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____12973
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____12970
                                         in
                                      ([], uu____12969)
                                  | uu____12985 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____12995 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____12995
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13011 =
                                          let uu____13019 =
                                            let uu____13020 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13021 =
                                              let uu____13037 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13037)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13020 uu____13021
                                             in
                                          (uu____13019,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13011
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____12956 with
                                | (tok_decls,env2) ->
                                    let uu____13064 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13064
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____12888 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13092 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13092 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13114 =
                                               let uu____13115 =
                                                 let uu____13123 =
                                                   let uu____13124 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13124
                                                    in
                                                 (uu____13123,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13115
                                                in
                                             [uu____13114]
                                           else []  in
                                         let uu____13132 =
                                           let uu____13135 =
                                             let uu____13138 =
                                               let uu____13139 =
                                                 let uu____13147 =
                                                   let uu____13148 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____13149 =
                                                     let uu____13160 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13160)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____13148 uu____13149
                                                    in
                                                 (uu____13147,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13139
                                                in
                                             [uu____13138]  in
                                           FStar_List.append karr uu____13135
                                            in
                                         FStar_List.append decls1 uu____13132
                                      in
                                   let aux =
                                     let uu____13175 =
                                       let uu____13178 =
                                         inversion_axioms tapp vars  in
                                       let uu____13181 =
                                         let uu____13184 =
                                           let uu____13185 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____13185 env2
                                             tapp vars
                                            in
                                         [uu____13184]  in
                                       FStar_List.append uu____13178
                                         uu____13181
                                        in
                                     FStar_List.append kindingAx uu____13175
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13190,uu____13191,uu____13192,uu____13193,uu____13194)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13202,t,uu____13204,n_tps,uu____13206) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____13216 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____13216 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____13264 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____13264 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____13292 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____13292 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13312 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____13312 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____13391 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____13391,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____13398 =
                                  let uu____13399 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____13399, true)
                                   in
                                let uu____13407 =
                                  let uu____13414 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____13414
                                   in
                                FStar_All.pipe_right uu____13398 uu____13407
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
                              let uu____13426 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____13426 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____13438::uu____13439 ->
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
                                         let uu____13498 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____13499 =
                                           let uu____13510 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____13510)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13498 uu____13499
                                     | uu____13531 -> tok_typing  in
                                   let uu____13542 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____13542 with
                                    | (vars',guards',env'',decls_formals,uu____13567)
                                        ->
                                        let uu____13580 =
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
                                        (match uu____13580 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____13610 ->
                                                   let uu____13619 =
                                                     let uu____13620 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____13620
                                                      in
                                                   [uu____13619]
                                                in
                                             let encode_elim uu____13636 =
                                               let uu____13637 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____13637 with
                                               | (head1,args) ->
                                                   let uu____13688 =
                                                     let uu____13689 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____13689.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____13688 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____13701;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____13702;_},uu____13703)
                                                        ->
                                                        let uu____13708 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____13708
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____13729
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____13729
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
                                                                    uu____13783
                                                                    ->
                                                                    let uu____13784
                                                                    =
                                                                    let uu____13790
                                                                    =
                                                                    let uu____13792
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13792
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13790)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13784
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13812
                                                                    =
                                                                    let uu____13814
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13814
                                                                     in
                                                                    if
                                                                    uu____13812
                                                                    then
                                                                    let uu____13830
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13830]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____13833
                                                                    =
                                                                    let uu____13847
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____13904
                                                                     ->
                                                                    fun
                                                                    uu____13905
                                                                     ->
                                                                    match 
                                                                    (uu____13904,
                                                                    uu____13905)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14016
                                                                    =
                                                                    let uu____14024
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14024
                                                                     in
                                                                    (match uu____14016
                                                                    with
                                                                    | 
                                                                    (uu____14038,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14049
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14049
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14054
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14054
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
                                                                    uu____13847
                                                                     in
                                                                  (match uu____13833
                                                                   with
                                                                   | 
                                                                   (uu____14075,arg_vars,elim_eqns_or_guards,uu____14078)
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
                                                                    let uu____14105
                                                                    =
                                                                    let uu____14113
                                                                    =
                                                                    let uu____14114
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14115
                                                                    =
                                                                    let uu____14126
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14128
                                                                    =
                                                                    let uu____14129
                                                                    =
                                                                    let uu____14134
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14134)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14129
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14126,
                                                                    uu____14128)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14114
                                                                    uu____14115
                                                                     in
                                                                    (uu____14113,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14105
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14149
                                                                    =
                                                                    let uu____14155
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14155,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14149
                                                                     in
                                                                    let uu____14158
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14158
                                                                    then
                                                                    let x =
                                                                    let uu____14167
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14167,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14172
                                                                    =
                                                                    let uu____14180
                                                                    =
                                                                    let uu____14181
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14182
                                                                    =
                                                                    let uu____14193
                                                                    =
                                                                    let uu____14198
                                                                    =
                                                                    let uu____14201
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14201]
                                                                     in
                                                                    [uu____14198]
                                                                     in
                                                                    let uu____14206
                                                                    =
                                                                    let uu____14207
                                                                    =
                                                                    let uu____14212
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14214
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14212,
                                                                    uu____14214)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14207
                                                                     in
                                                                    (uu____14193,
                                                                    [x],
                                                                    uu____14206)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14181
                                                                    uu____14182
                                                                     in
                                                                    let uu____14229
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14180,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14229)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14172
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14240
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
                                                                    (let uu____14278
                                                                    =
                                                                    let uu____14279
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14279
                                                                    dapp1  in
                                                                    [uu____14278])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14240
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14286
                                                                    =
                                                                    let uu____14294
                                                                    =
                                                                    let uu____14295
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14296
                                                                    =
                                                                    let uu____14307
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14309
                                                                    =
                                                                    let uu____14310
                                                                    =
                                                                    let uu____14315
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14315)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14310
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14307,
                                                                    uu____14309)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14295
                                                                    uu____14296
                                                                     in
                                                                    (uu____14294,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14286)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____14333 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14333
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14354
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14354
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
                                                                    uu____14408
                                                                    ->
                                                                    let uu____14409
                                                                    =
                                                                    let uu____14415
                                                                    =
                                                                    let uu____14417
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14417
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14415)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14409
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14437
                                                                    =
                                                                    let uu____14439
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14439
                                                                     in
                                                                    if
                                                                    uu____14437
                                                                    then
                                                                    let uu____14455
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14455]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14458
                                                                    =
                                                                    let uu____14472
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14529
                                                                     ->
                                                                    fun
                                                                    uu____14530
                                                                     ->
                                                                    match 
                                                                    (uu____14529,
                                                                    uu____14530)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14649
                                                                     in
                                                                    (match uu____14641
                                                                    with
                                                                    | 
                                                                    (uu____14663,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14674
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14674
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14679
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14679
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
                                                                    uu____14472
                                                                     in
                                                                  (match uu____14458
                                                                   with
                                                                   | 
                                                                   (uu____14700,arg_vars,elim_eqns_or_guards,uu____14703)
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
                                                                    let uu____14730
                                                                    =
                                                                    let uu____14738
                                                                    =
                                                                    let uu____14739
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14740
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14753
                                                                    =
                                                                    let uu____14754
                                                                    =
                                                                    let uu____14759
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14759)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14754
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14751,
                                                                    uu____14753)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14739
                                                                    uu____14740
                                                                     in
                                                                    (uu____14738,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14730
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14774
                                                                    =
                                                                    let uu____14780
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14780,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14774
                                                                     in
                                                                    let uu____14783
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14783
                                                                    then
                                                                    let x =
                                                                    let uu____14792
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14792,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14797
                                                                    =
                                                                    let uu____14805
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14807
                                                                    =
                                                                    let uu____14818
                                                                    =
                                                                    let uu____14823
                                                                    =
                                                                    let uu____14826
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14826]
                                                                     in
                                                                    [uu____14823]
                                                                     in
                                                                    let uu____14831
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    let uu____14837
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14839
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14837,
                                                                    uu____14839)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14832
                                                                     in
                                                                    (uu____14818,
                                                                    [x],
                                                                    uu____14831)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14806
                                                                    uu____14807
                                                                     in
                                                                    let uu____14854
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14805,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14854)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14797
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14865
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
                                                                    (let uu____14903
                                                                    =
                                                                    let uu____14904
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14904
                                                                    dapp1  in
                                                                    [uu____14903])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14865
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14911
                                                                    =
                                                                    let uu____14919
                                                                    =
                                                                    let uu____14920
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14921
                                                                    =
                                                                    let uu____14932
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14934
                                                                    =
                                                                    let uu____14935
                                                                    =
                                                                    let uu____14940
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14940)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14935
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14932,
                                                                    uu____14934)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14920
                                                                    uu____14921
                                                                     in
                                                                    (uu____14919,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14911)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____14957 ->
                                                        ((let uu____14959 =
                                                            let uu____14965 =
                                                              let uu____14967
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____14969
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____14967
                                                                uu____14969
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____14965)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14959);
                                                         ([], [])))
                                                in
                                             let uu____14977 = encode_elim ()
                                                in
                                             (match uu____14977 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15003 =
                                                      let uu____15006 =
                                                        let uu____15009 =
                                                          let uu____15012 =
                                                            let uu____15015 =
                                                              let uu____15016
                                                                =
                                                                let uu____15028
                                                                  =
                                                                  let uu____15029
                                                                    =
                                                                    let uu____15031
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15031
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15029
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15028)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15016
                                                               in
                                                            [uu____15015]  in
                                                          let uu____15038 =
                                                            let uu____15041 =
                                                              let uu____15044
                                                                =
                                                                let uu____15047
                                                                  =
                                                                  let uu____15050
                                                                    =
                                                                    let uu____15053
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15058
                                                                    =
                                                                    let uu____15061
                                                                    =
                                                                    let uu____15062
                                                                    =
                                                                    let uu____15070
                                                                    =
                                                                    let uu____15071
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15072
                                                                    =
                                                                    let uu____15083
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15083)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15071
                                                                    uu____15072
                                                                     in
                                                                    (uu____15070,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15062
                                                                     in
                                                                    let uu____15096
                                                                    =
                                                                    let uu____15099
                                                                    =
                                                                    let uu____15100
                                                                    =
                                                                    let uu____15108
                                                                    =
                                                                    let uu____15109
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15110
                                                                    =
                                                                    let uu____15121
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15123
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15121,
                                                                    uu____15123)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15109
                                                                    uu____15110
                                                                     in
                                                                    (uu____15108,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15100
                                                                     in
                                                                    [uu____15099]
                                                                     in
                                                                    uu____15061
                                                                    ::
                                                                    uu____15096
                                                                     in
                                                                    uu____15053
                                                                    ::
                                                                    uu____15058
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15050
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15047
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15044
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15041
                                                             in
                                                          FStar_List.append
                                                            uu____15012
                                                            uu____15038
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15009
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15006
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15003
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
           (fun uu____15161  ->
              fun se  ->
                match uu____15161 with
                | (g,env1) ->
                    let uu____15181 = encode_sigelt env1 se  in
                    (match uu____15181 with
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
      let encode_binding b uu____15249 =
        match uu____15249 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15286 ->
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
                 ((let uu____15294 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15294
                   then
                     let uu____15299 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15301 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15303 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15299 uu____15301 uu____15303
                   else ());
                  (let uu____15308 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15308 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15326 =
                         let uu____15334 =
                           let uu____15336 =
                             let uu____15338 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15338
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15336  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15334
                          in
                       (match uu____15326 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15358 = FStar_Options.log_queries ()
                                 in
                              if uu____15358
                              then
                                let uu____15361 =
                                  let uu____15363 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15365 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15367 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15363 uu____15365 uu____15367
                                   in
                                FStar_Pervasives_Native.Some uu____15361
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15391,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15411 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15411 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15438 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15438 with | (uu____15465,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____15481 'Auu____15482 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____15481,'Auu____15482)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15555  ->
              match uu____15555 with
              | (l,uu____15568,uu____15569) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15620  ->
              match uu____15620 with
              | (l,uu____15635,uu____15636) ->
                  let uu____15647 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____15650 =
                    let uu____15653 =
                      let uu____15654 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15654  in
                    [uu____15653]  in
                  uu____15647 :: uu____15650))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15683 =
      let uu____15686 =
        let uu____15687 = FStar_Util.psmap_empty ()  in
        let uu____15702 = FStar_Util.psmap_empty ()  in
        let uu____15705 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15709 =
          let uu____15711 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15711 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15687;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15702;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____15705;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15709;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____15686]  in
    FStar_ST.op_Colon_Equals last_env uu____15683
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15753 = FStar_ST.op_Bang last_env  in
      match uu____15753 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15781 ->
          let uu___396_15784 = e  in
          let uu____15785 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___396_15784.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___396_15784.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___396_15784.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___396_15784.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___396_15784.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___396_15784.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___396_15784.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___396_15784.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15785;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___396_15784.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15793 = FStar_ST.op_Bang last_env  in
    match uu____15793 with
    | [] -> failwith "Empty env stack"
    | uu____15820::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15852  ->
    let uu____15853 = FStar_ST.op_Bang last_env  in
    match uu____15853 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15913  ->
    let uu____15914 = FStar_ST.op_Bang last_env  in
    match uu____15914 with
    | [] -> failwith "Popping an empty stack"
    | uu____15941::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____15978  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16031  ->
         let uu____16032 = snapshot_env ()  in
         match uu____16032 with
         | (env_depth,()) ->
             let uu____16054 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16054 with
              | (varops_depth,()) ->
                  let uu____16076 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16076 with
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
        (fun uu____16134  ->
           let uu____16135 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16135 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16230 = snapshot msg  in () 
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
        | (uu____16276::uu____16277,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___397_16285 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___397_16285.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___397_16285.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___397_16285.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16286 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16306 =
        let uu____16309 =
          let uu____16310 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16310  in
        let uu____16311 = open_fact_db_tags env  in uu____16309 ::
          uu____16311
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16306
  
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
      let uu____16338 = encode_sigelt env se  in
      match uu____16338 with
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
        let uu____16383 = FStar_Options.log_queries ()  in
        if uu____16383
        then
          let uu____16388 =
            let uu____16389 =
              let uu____16391 =
                let uu____16393 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16393 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16391  in
            FStar_SMTEncoding_Term.Caption uu____16389  in
          uu____16388 :: decls
        else decls  in
      (let uu____16412 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____16412
       then
         let uu____16415 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16415
       else ());
      (let env =
         let uu____16421 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16421 tcenv  in
       let uu____16422 = encode_top_level_facts env se  in
       match uu____16422 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16436 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16436)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16450 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16450
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16465 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____16465
          then
            let uu____16468 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16468
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16514  ->
                    fun se  ->
                      match uu____16514 with
                      | (g,env2) ->
                          let uu____16534 = encode_top_level_facts env2 se
                             in
                          (match uu____16534 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16557 =
            encode_signature
              (let uu___398_16566 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___398_16566.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___398_16566.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___398_16566.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___398_16566.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___398_16566.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___398_16566.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___398_16566.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___398_16566.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___398_16566.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___398_16566.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16557 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____16586 = FStar_Options.log_queries ()  in
                if uu____16586
                then
                  let msg = Prims.strcat "Externals for " name  in
                  FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
                else decls1  in
              (set_env
                 (let uu___399_16600 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___399_16600.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___399_16600.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___399_16600.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___399_16600.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___399_16600.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___399_16600.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___399_16600.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___399_16600.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___399_16600.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___399_16600.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____16603 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____16603
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let decls1 = caption decls  in
                FStar_SMTEncoding_Z3.giveZ3 decls1))))
  
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
        (let uu____16668 =
           let uu____16670 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16670.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16668);
        (let env =
           let uu____16672 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16672 tcenv  in
         let uu____16673 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16712 = aux rest  in
                 (match uu____16712 with
                  | (out,rest1) ->
                      let t =
                        let uu____16740 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16740 with
                        | FStar_Pervasives_Native.Some uu____16743 ->
                            let uu____16744 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16744
                              x.FStar_Syntax_Syntax.sort
                        | uu____16745 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16749 =
                        let uu____16752 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___400_16755 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___400_16755.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___400_16755.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16752 :: out  in
                      (uu____16749, rest1))
             | uu____16760 -> ([], bindings)  in
           let uu____16767 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16767 with
           | (closing,bindings) ->
               let uu____16794 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16794, bindings)
            in
         match uu____16673 with
         | (q1,bindings) ->
             let uu____16825 = encode_env_bindings env bindings  in
             (match uu____16825 with
              | (env_decls,env1) ->
                  ((let uu____16847 =
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
                    if uu____16847
                    then
                      let uu____16854 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16854
                    else ());
                   (let uu____16859 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16859 with
                    | (phi,qdecls) ->
                        let uu____16880 =
                          let uu____16885 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16885 phi
                           in
                        (match uu____16880 with
                         | (labels,phi1) ->
                             let uu____16902 = encode_labels labels  in
                             (match uu____16902 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____16940 =
                                      let uu____16948 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16949 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____16948,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16949)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16940
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
  