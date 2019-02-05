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
    let uu____2707 =
      let uu____2708 =
        let uu____2716 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2716, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2708  in
    let uu____2721 =
      let uu____2724 =
        let uu____2725 =
          let uu____2733 =
            let uu____2734 =
              let uu____2745 =
                let uu____2746 =
                  let uu____2751 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2751)  in
                FStar_SMTEncoding_Util.mkImp uu____2746  in
              ([[typing_pred]], [xx], uu____2745)  in
            let uu____2770 =
              let uu____2785 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2785  in
            uu____2770 uu____2734  in
          (uu____2733, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2725  in
      [uu____2724]  in
    uu____2707 :: uu____2721  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2820 =
      let uu____2821 =
        let uu____2829 =
          let uu____2830 = FStar_TypeChecker_Env.get_range env  in
          let uu____2831 =
            let uu____2842 =
              let uu____2847 =
                let uu____2850 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2850]  in
              [uu____2847]  in
            let uu____2855 =
              let uu____2856 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2856 tt  in
            (uu____2842, [bb], uu____2855)  in
          FStar_SMTEncoding_Term.mkForall uu____2830 uu____2831  in
        (uu____2829, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2821  in
    let uu____2875 =
      let uu____2878 =
        let uu____2879 =
          let uu____2887 =
            let uu____2888 =
              let uu____2899 =
                let uu____2900 =
                  let uu____2905 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2905)  in
                FStar_SMTEncoding_Util.mkImp uu____2900  in
              ([[typing_pred]], [xx], uu____2899)  in
            let uu____2926 =
              let uu____2941 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2941  in
            uu____2926 uu____2888  in
          (uu____2887, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2879  in
      [uu____2878]  in
    uu____2820 :: uu____2875  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____2967 =
        let uu____2973 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____2973, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____2967  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____2997 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2997  in
    let uu____3002 =
      let uu____3003 =
        let uu____3011 =
          let uu____3012 = FStar_TypeChecker_Env.get_range env  in
          let uu____3013 =
            let uu____3024 =
              let uu____3029 =
                let uu____3032 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3032]  in
              [uu____3029]  in
            let uu____3037 =
              let uu____3038 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3038 tt  in
            (uu____3024, [bb], uu____3037)  in
          FStar_SMTEncoding_Term.mkForall uu____3012 uu____3013  in
        (uu____3011, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3003  in
    let uu____3057 =
      let uu____3060 =
        let uu____3061 =
          let uu____3069 =
            let uu____3070 =
              let uu____3081 =
                let uu____3082 =
                  let uu____3087 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3087)  in
                FStar_SMTEncoding_Util.mkImp uu____3082  in
              ([[typing_pred]], [xx], uu____3081)  in
            let uu____3108 =
              let uu____3123 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3123  in
            uu____3108 uu____3070  in
          (uu____3069, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3061  in
      let uu____3128 =
        let uu____3131 =
          let uu____3132 =
            let uu____3140 =
              let uu____3141 =
                let uu____3152 =
                  let uu____3153 =
                    let uu____3158 =
                      let uu____3159 =
                        let uu____3162 =
                          let uu____3165 =
                            let uu____3168 =
                              let uu____3169 =
                                let uu____3174 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3175 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3174, uu____3175)  in
                              FStar_SMTEncoding_Util.mkGT uu____3169  in
                            let uu____3177 =
                              let uu____3180 =
                                let uu____3181 =
                                  let uu____3186 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3187 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3186, uu____3187)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3181  in
                              let uu____3189 =
                                let uu____3192 =
                                  let uu____3193 =
                                    let uu____3198 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3199 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3198, uu____3199)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3193  in
                                [uu____3192]  in
                              uu____3180 :: uu____3189  in
                            uu____3168 :: uu____3177  in
                          typing_pred_y :: uu____3165  in
                        typing_pred :: uu____3162  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3159  in
                    (uu____3158, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3153  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3152)
                 in
              let uu____3223 =
                let uu____3238 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3238  in
              uu____3223 uu____3141  in
            (uu____3140,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3132  in
        [uu____3131]  in
      uu____3060 :: uu____3128  in
    uu____3002 :: uu____3057  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3273 =
      let uu____3274 =
        let uu____3282 =
          let uu____3283 = FStar_TypeChecker_Env.get_range env  in
          let uu____3284 =
            let uu____3295 =
              let uu____3300 =
                let uu____3303 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3303]  in
              [uu____3300]  in
            let uu____3308 =
              let uu____3309 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3309 tt  in
            (uu____3295, [bb], uu____3308)  in
          FStar_SMTEncoding_Term.mkForall uu____3283 uu____3284  in
        (uu____3282, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3274  in
    let uu____3328 =
      let uu____3331 =
        let uu____3332 =
          let uu____3340 =
            let uu____3341 =
              let uu____3352 =
                let uu____3353 =
                  let uu____3358 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3358)  in
                FStar_SMTEncoding_Util.mkImp uu____3353  in
              ([[typing_pred]], [xx], uu____3352)  in
            let uu____3379 =
              let uu____3394 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3394  in
            uu____3379 uu____3341  in
          (uu____3340, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3332  in
      [uu____3331]  in
    uu____3273 :: uu____3328  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3424 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3424]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3454 =
      let uu____3455 =
        let uu____3463 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3463, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3455  in
    [uu____3454]  in
  let mk_and_interp env conj uu____3486 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3525 =
      let uu____3526 =
        let uu____3534 =
          let uu____3535 = FStar_TypeChecker_Env.get_range env  in
          let uu____3536 =
            let uu____3547 =
              let uu____3548 =
                let uu____3553 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3553, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3548  in
            ([[l_and_a_b]], [aa; bb], uu____3547)  in
          FStar_SMTEncoding_Term.mkForall uu____3535 uu____3536  in
        (uu____3534, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3526  in
    [uu____3525]  in
  let mk_or_interp env disj uu____3599 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3638 =
      let uu____3639 =
        let uu____3647 =
          let uu____3648 = FStar_TypeChecker_Env.get_range env  in
          let uu____3649 =
            let uu____3660 =
              let uu____3661 =
                let uu____3666 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3666, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3661  in
            ([[l_or_a_b]], [aa; bb], uu____3660)  in
          FStar_SMTEncoding_Term.mkForall uu____3648 uu____3649  in
        (uu____3647, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3639  in
    [uu____3638]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3750 =
      let uu____3751 =
        let uu____3759 =
          let uu____3760 = FStar_TypeChecker_Env.get_range env  in
          let uu____3761 =
            let uu____3772 =
              let uu____3773 =
                let uu____3778 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3778, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3773  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3772)  in
          FStar_SMTEncoding_Term.mkForall uu____3760 uu____3761  in
        (uu____3759, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3751  in
    [uu____3750]  in
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
    let uu____3876 =
      let uu____3877 =
        let uu____3885 =
          let uu____3886 = FStar_TypeChecker_Env.get_range env  in
          let uu____3887 =
            let uu____3898 =
              let uu____3899 =
                let uu____3904 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3904, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3899  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3898)  in
          FStar_SMTEncoding_Term.mkForall uu____3886 uu____3887  in
        (uu____3885, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3877  in
    [uu____3876]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3999 =
      let uu____4000 =
        let uu____4008 =
          let uu____4009 = FStar_TypeChecker_Env.get_range env  in
          let uu____4010 =
            let uu____4021 =
              let uu____4022 =
                let uu____4027 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____4027, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4022  in
            ([[l_imp_a_b]], [aa; bb], uu____4021)  in
          FStar_SMTEncoding_Term.mkForall uu____4009 uu____4010  in
        (uu____4008, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4000  in
    [uu____3999]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____4112 =
      let uu____4113 =
        let uu____4121 =
          let uu____4122 = FStar_TypeChecker_Env.get_range env  in
          let uu____4123 =
            let uu____4134 =
              let uu____4135 =
                let uu____4140 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4140, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4135  in
            ([[l_iff_a_b]], [aa; bb], uu____4134)  in
          FStar_SMTEncoding_Term.mkForall uu____4122 uu____4123  in
        (uu____4121, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4113  in
    [uu____4112]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4207 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4207  in
    let uu____4212 =
      let uu____4213 =
        let uu____4221 =
          let uu____4222 = FStar_TypeChecker_Env.get_range env  in
          let uu____4223 =
            let uu____4234 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4234)  in
          FStar_SMTEncoding_Term.mkForall uu____4222 uu____4223  in
        (uu____4221, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4213  in
    [uu____4212]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4281 =
      let uu____4282 =
        let uu____4290 =
          let uu____4291 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4291 range_ty  in
        let uu____4292 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4290, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4292)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4282  in
    [uu____4281]  in
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
        let uu____4348 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4348 x1 t  in
      let uu____4350 = FStar_TypeChecker_Env.get_range env  in
      let uu____4351 =
        let uu____4362 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4362)  in
      FStar_SMTEncoding_Term.mkForall uu____4350 uu____4351  in
    let uu____4381 =
      let uu____4382 =
        let uu____4390 =
          let uu____4391 = FStar_TypeChecker_Env.get_range env  in
          let uu____4392 =
            let uu____4403 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4403)  in
          FStar_SMTEncoding_Term.mkForall uu____4391 uu____4392  in
        (uu____4390,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4382  in
    [uu____4381]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4468 =
      let uu____4469 =
        let uu____4477 =
          let uu____4478 = FStar_TypeChecker_Env.get_range env  in
          let uu____4479 =
            let uu____4495 =
              let uu____4496 =
                let uu____4501 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4502 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4501, uu____4502)  in
              FStar_SMTEncoding_Util.mkAnd uu____4496  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4495)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4478 uu____4479  in
        (uu____4477,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4469  in
    [uu____4468]  in
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
          let uu____5023 =
            FStar_Util.find_opt
              (fun uu____5061  ->
                 match uu____5061 with
                 | (l,uu____5077) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5023 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____5120,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5181 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5181 with
        | (form,decls) ->
            let uu____5190 =
              let uu____5193 =
                let uu____5196 =
                  FStar_SMTEncoding_Util.mkAssume
                    (form,
                      (FStar_Pervasives_Native.Some
                         (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                      (Prims.strcat "lemma_" lid.FStar_Ident.str))
                   in
                [uu____5196]  in
              FStar_All.pipe_right uu____5193
                FStar_SMTEncoding_Term.mk_decls_trivial
               in
            FStar_List.append decls uu____5190
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
              let uu____5259 =
                ((let uu____5263 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5263) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5259
              then
                let arg_sorts =
                  let uu____5275 =
                    let uu____5276 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5276.FStar_Syntax_Syntax.n  in
                  match uu____5275 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5282) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5320  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5327 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5329 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5329 with
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
                    let uu____5365 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    (uu____5365, env1)
              else
                (let uu____5370 = prims.is lid  in
                 if uu____5370
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5379 = prims.mk lid vname  in
                   match uu____5379 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       let uu____5403 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial
                          in
                       (uu____5403, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5412 =
                      let uu____5431 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5431 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5459 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5459
                            then
                              let uu____5464 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___386_5467 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___386_5467.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___386_5467.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___386_5467.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___386_5467.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___386_5467.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___386_5467.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___386_5467.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___386_5467.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___386_5467.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___386_5467.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___386_5467.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___386_5467.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___386_5467.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___386_5467.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___386_5467.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___386_5467.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___386_5467.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___386_5467.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___386_5467.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___386_5467.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___386_5467.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___386_5467.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___386_5467.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___386_5467.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___386_5467.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___386_5467.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___386_5467.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___386_5467.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___386_5467.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___386_5467.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___386_5467.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___386_5467.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___386_5467.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___386_5467.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___386_5467.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___386_5467.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___386_5467.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___386_5467.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___386_5467.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___386_5467.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___386_5467.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___386_5467.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5464
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5490 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5490)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5412 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____5569 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____5569 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____5601 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___375_5662  ->
                                       match uu___375_5662 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____5666 =
                                             FStar_Util.prefix vars  in
                                           (match uu____5666 with
                                            | (uu____5690,(xxsym,uu____5692))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____5716 =
                                                  let uu____5717 =
                                                    let uu____5725 =
                                                      let uu____5726 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5727 =
                                                        let uu____5738 =
                                                          let uu____5739 =
                                                            let uu____5744 =
                                                              let uu____5745
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____5745
                                                               in
                                                            (vapp,
                                                              uu____5744)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____5739
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5738)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5726 uu____5727
                                                       in
                                                    (uu____5725,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5717
                                                   in
                                                [uu____5716])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____5760 =
                                             FStar_Util.prefix vars  in
                                           (match uu____5760 with
                                            | (uu____5784,(xxsym,uu____5786))
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
                                                let uu____5818 =
                                                  let uu____5819 =
                                                    let uu____5827 =
                                                      let uu____5828 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5829 =
                                                        let uu____5840 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5840)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5828 uu____5829
                                                       in
                                                    (uu____5827,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5819
                                                   in
                                                [uu____5818])
                                       | uu____5853 -> []))
                                in
                             let uu____5854 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5854 with
                              | (vars,guards,env',decls1,uu____5879) ->
                                  let uu____5892 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5905 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5905, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5909 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5909 with
                                         | (g,ds) ->
                                             let uu____5922 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5922,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5892 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5937 =
                                           let uu____5945 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5945)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5937
                                          in
                                       let uu____5951 =
                                         let vname_decl =
                                           let uu____5959 =
                                             let uu____5971 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5991  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5971,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5959
                                            in
                                         let uu____6002 =
                                           let env2 =
                                             let uu___387_6008 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.encoding_quantifier);
                                               FStar_SMTEncoding_Env.global_cache
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.global_cache);
                                               FStar_SMTEncoding_Env.local_cache
                                                 =
                                                 (uu___387_6008.FStar_SMTEncoding_Env.local_cache)
                                             }  in
                                           let uu____6009 =
                                             let uu____6011 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6011  in
                                           if uu____6009
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6002 with
                                         | (tok_typing,decls2) ->
                                             let uu____6028 =
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
                                                   let uu____6052 =
                                                     let uu____6055 =
                                                       FStar_All.pipe_right
                                                         [tok_typing1]
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append decls2
                                                       uu____6055
                                                      in
                                                   let uu____6062 =
                                                     let uu____6063 =
                                                       let uu____6066 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6066
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6063
                                                      in
                                                   (uu____6052, uu____6062)
                                               | uu____6076 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6091 =
                                                       let uu____6099 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6099]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6091
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6121 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6122 =
                                                       let uu____6133 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6133)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6121 uu____6122
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6143 =
                                                       let uu____6151 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6151,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6143
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
                                                       let uu____6190 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6191 =
                                                         let uu____6202 =
                                                           let uu____6203 =
                                                             let uu____6208 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6209 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6208,
                                                               uu____6209)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6203
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6202)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6190
                                                         uu____6191
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (guarded_tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname))
                                                      in
                                                   let uu____6232 =
                                                     let uu____6235 =
                                                       FStar_All.pipe_right
                                                         [vtok_decl;
                                                         name_tok_corr;
                                                         tok_typing1]
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append decls2
                                                       uu____6235
                                                      in
                                                   (uu____6232, env1)
                                                in
                                             (match uu____6028 with
                                              | (tok_decl,env2) ->
                                                  let uu____6256 =
                                                    let uu____6259 =
                                                      FStar_All.pipe_right
                                                        [vname_decl]
                                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                                       in
                                                    FStar_List.append
                                                      uu____6259 tok_decl
                                                     in
                                                  (uu____6256, env2))
                                          in
                                       (match uu____5951 with
                                        | (decls2,env2) ->
                                            let uu____6278 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____6288 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____6288 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____6303 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____6303,
                                                    decls)
                                               in
                                            (match uu____6278 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____6318 =
                                                     let uu____6326 =
                                                       let uu____6327 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6328 =
                                                         let uu____6339 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____6339)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6327
                                                         uu____6328
                                                        in
                                                     (uu____6326,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____6318
                                                    in
                                                 let freshness =
                                                   let uu____6355 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____6355
                                                   then
                                                     let uu____6363 =
                                                       let uu____6364 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6365 =
                                                         let uu____6378 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____6396 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____6378,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____6396)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____6364
                                                         uu____6365
                                                        in
                                                     let uu____6402 =
                                                       let uu____6405 =
                                                         let uu____6406 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____6406 env2
                                                           vapp vars
                                                          in
                                                       [uu____6405]  in
                                                     uu____6363 :: uu____6402
                                                   else []  in
                                                 let g =
                                                   let uu____6412 =
                                                     let uu____6415 =
                                                       let uu____6418 =
                                                         let uu____6421 =
                                                           let uu____6424 =
                                                             let uu____6427 =
                                                               mk_disc_proj_axioms
                                                                 guard
                                                                 encoded_res_t
                                                                 vapp vars
                                                                in
                                                             typingAx ::
                                                               uu____6427
                                                              in
                                                           FStar_List.append
                                                             freshness
                                                             uu____6424
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6421
                                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____6418
                                                        in
                                                     FStar_List.append decls2
                                                       uu____6415
                                                      in
                                                   FStar_List.append decls11
                                                     uu____6412
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding *
            FStar_SMTEncoding_Term.decls_elt Prims.list *
            FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____6471 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6471 with
          | FStar_Pervasives_Native.None  ->
              let uu____6482 = encode_free_var false env x t t_norm []  in
              (match uu____6482 with
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
            let uu____6545 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6545 with
            | (decls,env1) ->
                let uu____6556 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6556
                then
                  let uu____6563 =
                    let uu____6564 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____6564  in
                  (uu____6563, env1)
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
             (fun uu____6620  ->
                fun lb  ->
                  match uu____6620 with
                  | (decls,env1) ->
                      let uu____6640 =
                        let uu____6645 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____6645
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____6640 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____6674 = FStar_Syntax_Util.head_and_args t  in
    match uu____6674 with
    | (hd1,args) ->
        let uu____6718 =
          let uu____6719 = FStar_Syntax_Util.un_uinst hd1  in
          uu____6719.FStar_Syntax_Syntax.n  in
        (match uu____6718 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____6725,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____6749 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____6760 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___388_6768 = en  in
    let uu____6769 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    let uu____6772 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.local_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___388_6768.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___388_6768.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___388_6768.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___388_6768.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___388_6768.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___388_6768.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___388_6768.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___388_6768.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___388_6768.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___388_6768.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____6769;
      FStar_SMTEncoding_Env.local_cache = uu____6772
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____6802  ->
      fun quals  ->
        match uu____6802 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____6907 = FStar_Util.first_N nbinders formals  in
              match uu____6907 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7008  ->
                         fun uu____7009  ->
                           match (uu____7008, uu____7009) with
                           | ((formal,uu____7035),(binder,uu____7037)) ->
                               let uu____7058 =
                                 let uu____7065 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7065)  in
                               FStar_Syntax_Syntax.NT uu____7058) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7079 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7120  ->
                              match uu____7120 with
                              | (x,i) ->
                                  let uu____7139 =
                                    let uu___389_7140 = x  in
                                    let uu____7141 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___389_7140.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___389_7140.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7141
                                    }  in
                                  (uu____7139, i)))
                       in
                    FStar_All.pipe_right uu____7079
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7165 =
                      let uu____7170 = FStar_Syntax_Subst.compress body  in
                      let uu____7171 =
                        let uu____7172 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7172
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7170 uu____7171
                       in
                    uu____7165 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t e =
              let tcenv =
                let uu___390_7228 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___390_7228.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___390_7228.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___390_7228.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___390_7228.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___390_7228.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___390_7228.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___390_7228.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___390_7228.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___390_7228.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___390_7228.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___390_7228.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___390_7228.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___390_7228.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___390_7228.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___390_7228.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___390_7228.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___390_7228.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___390_7228.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___390_7228.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___390_7228.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___390_7228.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___390_7228.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___390_7228.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___390_7228.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___390_7228.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___390_7228.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___390_7228.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___390_7228.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___390_7228.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___390_7228.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___390_7228.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___390_7228.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___390_7228.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___390_7228.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___390_7228.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___390_7228.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___390_7228.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___390_7228.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___390_7228.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___390_7228.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___390_7228.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___390_7228.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7300  ->
                       fun uu____7301  ->
                         match (uu____7300, uu____7301) with
                         | ((x,uu____7327),(b,uu____7329)) ->
                             let uu____7350 =
                               let uu____7357 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7357)  in
                             FStar_Syntax_Syntax.NT uu____7350) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7382 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7382
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7411 ->
                    let uu____7418 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7418
                | uu____7419 when Prims.op_Negation norm1 ->
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
                | uu____7422 ->
                    let uu____7423 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7423)
                 in
              let aux t1 e1 =
                let uu____7465 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7465 with
                | (binders,body,lopt) ->
                    let uu____7497 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7513 -> arrow_formals_comp_norm false t1  in
                    (match uu____7497 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7547 =
                           if nformals < nbinders
                           then
                             let uu____7591 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7591 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____7675 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____7675)
                           else
                             if nformals > nbinders
                             then
                               (let uu____7715 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____7715 with
                                | (binders1,body1) ->
                                    let uu____7768 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____7768))
                             else
                               (let uu____7781 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____7781))
                            in
                         (match uu____7547 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____7841 = aux t e  in
              match uu____7841 with
              | (binders,body,comp) ->
                  let uu____7887 =
                    let uu____7898 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____7898
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____7913 = aux comp1 body1  in
                      match uu____7913 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____7887 with
                   | (binders1,body1,comp1) ->
                       let uu____7996 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____7996, comp1))
               in
            (try
               (fun uu___392_8023  ->
                  match () with
                  | () ->
                      let uu____8030 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8030
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8046 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8109  ->
                                   fun lb  ->
                                     match uu____8109 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8164 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8164
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8170 =
                                             let uu____8179 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8179
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8170 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8046 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____8309 =
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
                               | uu____8322 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8332 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____8332 vars)
                                   else
                                     (let uu____8335 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____8335)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____8396;
                                    FStar_Syntax_Syntax.lbeff = uu____8397;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8399;
                                    FStar_Syntax_Syntax.lbpos = uu____8400;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8424 =
                                     let uu____8431 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8431 with
                                     | (tcenv',uu____8447,e_t) ->
                                         let uu____8453 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8464 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8453 with
                                          | (e1,t_norm1) ->
                                              ((let uu___393_8481 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.global_cache);
                                                  FStar_SMTEncoding_Env.local_cache
                                                    =
                                                    (uu___393_8481.FStar_SMTEncoding_Env.local_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8424 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8491 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____8491 with
                                         | (binders,body,t_body_comp) ->
                                             let curry =
                                               fvb.FStar_SMTEncoding_Env.smt_arity
                                                 <>
                                                 (FStar_List.length binders)
                                                in
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp
                                                in
                                             ((let uu____8520 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8520
                                               then
                                                 let uu____8525 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8528 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8525 uu____8528
                                               else ());
                                              (let uu____8533 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8533 with
                                               | (vars,_guards,env'1,binder_decls,uu____8560)
                                                   ->
                                                   let app =
                                                     let uu____8574 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     let uu____8575 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars
                                                        in
                                                     FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                       uu____8574 fvb
                                                       uu____8575
                                                      in
                                                   let uu____8578 =
                                                     let is_logical =
                                                       let uu____8591 =
                                                         let uu____8592 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____8592.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____8591 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____8598 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____8602 =
                                                         let uu____8603 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____8603
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____8602
                                                         (fun lid  ->
                                                            let uu____8612 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____8612
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____8613 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____8613
                                                     then
                                                       let uu____8629 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____8630 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body env'1
                                                          in
                                                       (app, uu____8629,
                                                         uu____8630)
                                                     else
                                                       (let uu____8641 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body env'1
                                                           in
                                                        (app, app,
                                                          uu____8641))
                                                      in
                                                   (match uu____8578 with
                                                    | (pat,app1,(body1,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____8665 =
                                                            let uu____8673 =
                                                              let uu____8674
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8675
                                                                =
                                                                let uu____8686
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____8686)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8674
                                                                uu____8675
                                                               in
                                                            let uu____8695 =
                                                              let uu____8696
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8696
                                                               in
                                                            (uu____8673,
                                                              uu____8695,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8665
                                                           in
                                                        let uu____8702 =
                                                          let uu____8705 =
                                                            let uu____8708 =
                                                              let uu____8711
                                                                =
                                                                let uu____8714
                                                                  =
                                                                  let uu____8717
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                  eqn ::
                                                                    uu____8717
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____8714
                                                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____8711
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____8708
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____8705
                                                           in
                                                        (uu____8702, env2))))))
                               | uu____8726 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____8791 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____8791,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____8797 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____8850  ->
                                         fun fvb  ->
                                           match uu____8850 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____8905 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8905
                                                  in
                                               let gtok =
                                                 let uu____8909 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8909
                                                  in
                                               let env4 =
                                                 let uu____8912 =
                                                   let uu____8915 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____8915
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____8912
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____8797 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9040
                                     t_norm uu____9042 =
                                     match (uu____9040, uu____9042) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9072;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9073;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9075;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9076;_})
                                         ->
                                         let uu____9103 =
                                           let uu____9110 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9110 with
                                           | (tcenv',uu____9126,e_t) ->
                                               let uu____9132 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9143 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9132 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___394_9160 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.global_cache);
                                                        FStar_SMTEncoding_Env.local_cache
                                                          =
                                                          (uu___394_9160.FStar_SMTEncoding_Env.local_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9103 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9173 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9173
                                                then
                                                  let uu____9178 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9180 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9182 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9178 uu____9180
                                                    uu____9182
                                                else ());
                                               (let uu____9187 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____9187 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9214 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9214 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9236 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9236
                                                           then
                                                             let uu____9241 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9243 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9246 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9248 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9241
                                                               uu____9243
                                                               uu____9246
                                                               uu____9248
                                                           else ());
                                                          (let uu____9253 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9253
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9282)
                                                               ->
                                                               let uu____9295
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9308,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9312
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9312
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9325
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9325,
                                                                    decls0))
                                                                  in
                                                               (match uu____9295
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
                                                                    let uu____9346
                                                                    =
                                                                    let uu____9358
                                                                    =
                                                                    let uu____9361
                                                                    =
                                                                    let uu____9364
                                                                    =
                                                                    let uu____9367
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9367
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    uu____9364
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9361
                                                                     in
                                                                    (g,
                                                                    uu____9358,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9346
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
                                                                    let uu____9398
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9398
                                                                     in
                                                                    let mk_g_app
                                                                    args =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    rng
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    g)
                                                                    (fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    (Prims.parse_int "1"))
                                                                    args  in
                                                                    let gsapp
                                                                    =
                                                                    let uu____9413
                                                                    =
                                                                    let uu____9416
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9416
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9413
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9422
                                                                    =
                                                                    let uu____9425
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9425
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9422
                                                                     in
                                                                    let uu____9430
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9430
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9446
                                                                    =
                                                                    let uu____9454
                                                                    =
                                                                    let uu____9455
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9456
                                                                    =
                                                                    let uu____9472
                                                                    =
                                                                    let uu____9473
                                                                    =
                                                                    let uu____9478
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9478)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9473
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9472)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9455
                                                                    uu____9456
                                                                     in
                                                                    let uu____9492
                                                                    =
                                                                    let uu____9493
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9493
                                                                     in
                                                                    (uu____9454,
                                                                    uu____9492,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9446
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9500
                                                                    =
                                                                    let uu____9508
                                                                    =
                                                                    let uu____9509
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9510
                                                                    =
                                                                    let uu____9521
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9521)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9509
                                                                    uu____9510
                                                                     in
                                                                    (uu____9508,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9500
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9535
                                                                    =
                                                                    let uu____9543
                                                                    =
                                                                    let uu____9544
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9545
                                                                    =
                                                                    let uu____9556
                                                                    =
                                                                    let uu____9557
                                                                    =
                                                                    let uu____9562
                                                                    =
                                                                    let uu____9563
                                                                    =
                                                                    let uu____9566
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9566
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9563
                                                                     in
                                                                    (gsapp,
                                                                    uu____9562)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9557
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9556)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9544
                                                                    uu____9545
                                                                     in
                                                                    (uu____9543,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9535
                                                                     in
                                                                    let uu____9580
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
                                                                    let uu____9592
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9592
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9594
                                                                    =
                                                                    let uu____9602
                                                                    =
                                                                    let uu____9603
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9604
                                                                    =
                                                                    let uu____9615
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9615)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9603
                                                                    uu____9604
                                                                     in
                                                                    (uu____9602,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9594
                                                                     in
                                                                    let uu____9628
                                                                    =
                                                                    let uu____9637
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____9637
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____9652
                                                                    =
                                                                    let uu____9655
                                                                    =
                                                                    let uu____9656
                                                                    =
                                                                    let uu____9664
                                                                    =
                                                                    let uu____9665
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9666
                                                                    =
                                                                    let uu____9677
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9677)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9665
                                                                    uu____9666
                                                                     in
                                                                    (uu____9664,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9656
                                                                     in
                                                                    [uu____9655]
                                                                     in
                                                                    (d3,
                                                                    uu____9652)
                                                                     in
                                                                    match uu____9628
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9580
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____9734
                                                                    =
                                                                    let uu____9737
                                                                    =
                                                                    let uu____9740
                                                                    =
                                                                    let uu____9743
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____9743
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____9740
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____9737
                                                                     in
                                                                    let uu____9750
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____9734,
                                                                    uu____9750,
                                                                    env02))))))))))
                                      in
                                   let uu____9755 =
                                     let uu____9768 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____9831  ->
                                          fun uu____9832  ->
                                            match (uu____9831, uu____9832)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____9957 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____9957 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____9768
                                      in
                                   (match uu____9755 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10024 =
                                          let isDeclFun uu___376_10041 =
                                            match uu___376_10041 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10043 -> true
                                            | uu____10056 -> false  in
                                          let uu____10058 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10058
                                            (fun decls3  ->
                                               let uu____10088 =
                                                 FStar_List.fold_left
                                                   (fun uu____10119  ->
                                                      fun elt  ->
                                                        match uu____10119
                                                        with
                                                        | (prefix_decls,elts,rest)
                                                            ->
                                                            let uu____10160 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls)
                                                               in
                                                            if uu____10160
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____10188
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls
                                                                  in
                                                               match uu____10188
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
                                                                    let uu___395_10226
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___395_10226.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___395_10226.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___395_10226.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3
                                                  in
                                               match uu____10088 with
                                               | (prefix_decls,elts,rest) ->
                                                   let uu____10258 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____10258, elts, rest))
                                           in
                                        (match uu____10024 with
                                         | (prefix_decls,elts,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01)))
                                in
                             let uu____10287 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___377_10293  ->
                                        match uu___377_10293 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10296 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10304 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10304)))
                                in
                             if uu____10287
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___397_10326  ->
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
                   let uu____10365 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10365
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____10384 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____10384, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____10440 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10440 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10446 = encode_sigelt' env se  in
      match uu____10446 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10458 =
                  let uu____10461 =
                    let uu____10462 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____10462  in
                  [uu____10461]  in
                FStar_All.pipe_right uu____10458
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____10467 ->
                let uu____10468 =
                  let uu____10471 =
                    let uu____10474 =
                      let uu____10475 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____10475  in
                    [uu____10474]  in
                  FStar_All.pipe_right uu____10471
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____10482 =
                  let uu____10485 =
                    let uu____10488 =
                      let uu____10491 =
                        let uu____10492 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____10492  in
                      [uu____10491]  in
                    FStar_All.pipe_right uu____10488
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____10485  in
                FStar_List.append uu____10468 uu____10482
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
        let uu____10512 =
          let uu____10513 = FStar_Syntax_Subst.compress t  in
          uu____10513.FStar_Syntax_Syntax.n  in
        match uu____10512 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10518)) -> s = "opaque_to_smt"
        | uu____10523 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____10532 =
          let uu____10533 = FStar_Syntax_Subst.compress t  in
          uu____10533.FStar_Syntax_Syntax.n  in
        match uu____10532 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10538)) -> s = "uninterpreted_by_smt"
        | uu____10543 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10549 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____10555 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____10567 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____10568 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10569 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10582 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10584 =
            let uu____10586 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____10586  in
          if uu____10584
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____10615 ->
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
               let uu____10647 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____10647 with
               | (formals,uu____10667) ->
                   let arity = FStar_List.length formals  in
                   let uu____10691 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____10691 with
                    | (aname,atok,env2) ->
                        let uu____10717 =
                          let uu____10722 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____10722 env2
                           in
                        (match uu____10717 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____10734 =
                                 let uu____10735 =
                                   let uu____10747 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____10767  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____10747,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____10735
                                  in
                               [uu____10734;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____10784 =
                               let aux uu____10845 uu____10846 =
                                 match (uu____10845, uu____10846) with
                                 | ((bv,uu____10905),(env3,acc_sorts,acc)) ->
                                     let uu____10952 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____10952 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____10784 with
                              | (uu____11036,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____11062 =
                                      let uu____11070 =
                                        let uu____11071 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11072 =
                                          let uu____11083 =
                                            let uu____11084 =
                                              let uu____11089 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____11089)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____11084
                                             in
                                          ([[app]], xs_sorts, uu____11083)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11071 uu____11072
                                         in
                                      (uu____11070,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11062
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
                                    let uu____11106 =
                                      let uu____11114 =
                                        let uu____11115 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11116 =
                                          let uu____11127 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____11127)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11115 uu____11116
                                         in
                                      (uu____11114,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11106
                                     in
                                  let uu____11140 =
                                    let uu____11143 =
                                      FStar_All.pipe_right
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence])
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append decls uu____11143  in
                                  (env2, uu____11140))))
                in
             let uu____11152 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____11152 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11178,uu____11179)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____11180 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____11180 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11202,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____11209 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___378_11215  ->
                      match uu___378_11215 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____11218 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____11224 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11227 -> false))
               in
            Prims.op_Negation uu____11209  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____11237 =
               let uu____11242 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____11242 env fv t quals  in
             match uu____11237 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____11257 =
                   let uu____11258 =
                     let uu____11261 =
                       primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                         lid tname tsym
                        in
                     FStar_All.pipe_right uu____11261
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   FStar_List.append decls uu____11258  in
                 (uu____11257, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____11271 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____11271 with
           | (uvs,f1) ->
               let env1 =
                 let uu___398_11283 = env  in
                 let uu____11284 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___398_11283.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___398_11283.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___398_11283.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____11284;
                   FStar_SMTEncoding_Env.warn =
                     (uu___398_11283.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___398_11283.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___398_11283.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___398_11283.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___398_11283.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___398_11283.FStar_SMTEncoding_Env.encoding_quantifier);
                   FStar_SMTEncoding_Env.global_cache =
                     (uu___398_11283.FStar_SMTEncoding_Env.global_cache);
                   FStar_SMTEncoding_Env.local_cache =
                     (uu___398_11283.FStar_SMTEncoding_Env.local_cache)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____11286 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____11286 with
                | (f3,decls) ->
                    let g =
                      let uu____11300 =
                        let uu____11303 =
                          let uu____11304 =
                            let uu____11312 =
                              let uu____11313 =
                                let uu____11315 =
                                  FStar_Syntax_Print.lid_to_string l  in
                                FStar_Util.format1 "Assumption: %s"
                                  uu____11315
                                 in
                              FStar_Pervasives_Native.Some uu____11313  in
                            let uu____11319 =
                              FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                (Prims.strcat "assumption_" l.FStar_Ident.str)
                               in
                            (f3, uu____11312, uu____11319)  in
                          FStar_SMTEncoding_Util.mkAssume uu____11304  in
                        [uu____11303]  in
                      FStar_All.pipe_right uu____11300
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____11328) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____11342 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____11364 =
                       let uu____11367 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____11367.FStar_Syntax_Syntax.fv_name  in
                     uu____11364.FStar_Syntax_Syntax.v  in
                   let uu____11368 =
                     let uu____11370 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____11370  in
                   if uu____11368
                   then
                     let val_decl =
                       let uu___399_11402 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___399_11402.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___399_11402.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___399_11402.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____11403 = encode_sigelt' env1 val_decl  in
                     match uu____11403 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____11342 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____11439,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____11441;
                          FStar_Syntax_Syntax.lbtyp = uu____11442;
                          FStar_Syntax_Syntax.lbeff = uu____11443;
                          FStar_Syntax_Syntax.lbdef = uu____11444;
                          FStar_Syntax_Syntax.lbattrs = uu____11445;
                          FStar_Syntax_Syntax.lbpos = uu____11446;_}::[]),uu____11447)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____11466 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____11466 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____11509 =
                   let uu____11512 =
                     let uu____11513 =
                       let uu____11521 =
                         let uu____11522 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____11523 =
                           let uu____11534 =
                             let uu____11535 =
                               let uu____11540 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____11540)  in
                             FStar_SMTEncoding_Util.mkEq uu____11535  in
                           ([[b2t_x]], [xx], uu____11534)  in
                         FStar_SMTEncoding_Term.mkForall uu____11522
                           uu____11523
                          in
                       (uu____11521,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11513  in
                   [uu____11512]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____11509
                  in
               let uu____11572 =
                 FStar_All.pipe_right decls
                   FStar_SMTEncoding_Term.mk_decls_trivial
                  in
               (uu____11572, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____11575,uu____11576) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___379_11586  ->
                  match uu___379_11586 with
                  | FStar_Syntax_Syntax.Discriminator uu____11588 -> true
                  | uu____11590 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____11592,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____11604 =
                     let uu____11606 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____11606.FStar_Ident.idText  in
                   uu____11604 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___380_11613  ->
                     match uu___380_11613 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____11616 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11619) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___381_11633  ->
                  match uu___381_11633 with
                  | FStar_Syntax_Syntax.Projector uu____11635 -> true
                  | uu____11641 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____11645 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____11645 with
           | FStar_Pervasives_Native.Some uu____11652 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___400_11654 = se  in
                 let uu____11655 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____11655;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___400_11654.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___400_11654.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___400_11654.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11658) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11673) ->
          let uu____11682 = encode_sigelts env ses  in
          (match uu____11682 with
           | (g,env1) ->
               let uu____11693 =
                 FStar_List.fold_left
                   (fun uu____11717  ->
                      fun elt  ->
                        match uu____11717 with
                        | (g',inversions) ->
                            let uu____11745 =
                              FStar_All.pipe_right
                                elt.FStar_SMTEncoding_Term.decls
                                (FStar_List.partition
                                   (fun uu___382_11768  ->
                                      match uu___382_11768 with
                                      | FStar_SMTEncoding_Term.Assume
                                          {
                                            FStar_SMTEncoding_Term.assumption_term
                                              = uu____11770;
                                            FStar_SMTEncoding_Term.assumption_caption
                                              = FStar_Pervasives_Native.Some
                                              "inversion axiom";
                                            FStar_SMTEncoding_Term.assumption_name
                                              = uu____11771;
                                            FStar_SMTEncoding_Term.assumption_fact_ids
                                              = uu____11772;_}
                                          -> false
                                      | uu____11779 -> true))
                               in
                            (match uu____11745 with
                             | (elt_g',elt_inversions) ->
                                 ((FStar_List.append g'
                                     [(let uu___401_11804 = elt  in
                                       {
                                         FStar_SMTEncoding_Term.sym_name =
                                           (uu___401_11804.FStar_SMTEncoding_Term.sym_name);
                                         FStar_SMTEncoding_Term.key =
                                           (uu___401_11804.FStar_SMTEncoding_Term.key);
                                         FStar_SMTEncoding_Term.decls =
                                           elt_g';
                                         FStar_SMTEncoding_Term.a_names =
                                           (uu___401_11804.FStar_SMTEncoding_Term.a_names)
                                       })]),
                                   (FStar_List.append inversions
                                      elt_inversions)))) ([], []) g
                  in
               (match uu____11693 with
                | (g',inversions) ->
                    let uu____11823 =
                      FStar_List.fold_left
                        (fun uu____11854  ->
                           fun elt  ->
                             match uu____11854 with
                             | (decls,elts,rest) ->
                                 let uu____11895 =
                                   (FStar_All.pipe_right
                                      elt.FStar_SMTEncoding_Term.key
                                      FStar_Util.is_some)
                                     &&
                                     (FStar_List.existsb
                                        (fun uu___383_11904  ->
                                           match uu___383_11904 with
                                           | FStar_SMTEncoding_Term.DeclFun
                                               uu____11906 -> true
                                           | uu____11919 -> false)
                                        elt.FStar_SMTEncoding_Term.decls)
                                    in
                                 if uu____11895
                                 then
                                   (decls, (FStar_List.append elts [elt]),
                                     rest)
                                 else
                                   (let uu____11942 =
                                      FStar_All.pipe_right
                                        elt.FStar_SMTEncoding_Term.decls
                                        (FStar_List.partition
                                           (fun uu___384_11963  ->
                                              match uu___384_11963 with
                                              | FStar_SMTEncoding_Term.DeclFun
                                                  uu____11965 -> true
                                              | uu____11978 -> false))
                                       in
                                    match uu____11942 with
                                    | (elt_decls,elt_rest) ->
                                        ((FStar_List.append decls elt_decls),
                                          elts,
                                          (FStar_List.append rest
                                             [(let uu___402_12009 = elt  in
                                               {
                                                 FStar_SMTEncoding_Term.sym_name
                                                   =
                                                   (uu___402_12009.FStar_SMTEncoding_Term.sym_name);
                                                 FStar_SMTEncoding_Term.key =
                                                   (uu___402_12009.FStar_SMTEncoding_Term.key);
                                                 FStar_SMTEncoding_Term.decls
                                                   = elt_rest;
                                                 FStar_SMTEncoding_Term.a_names
                                                   =
                                                   (uu___402_12009.FStar_SMTEncoding_Term.a_names)
                                               })])))) ([], [], []) g'
                       in
                    (match uu____11823 with
                     | (decls,elts,rest) ->
                         let uu____12035 =
                           let uu____12036 =
                             FStar_All.pipe_right decls
                               FStar_SMTEncoding_Term.mk_decls_trivial
                              in
                           let uu____12043 =
                             let uu____12046 =
                               let uu____12049 =
                                 FStar_All.pipe_right inversions
                                   FStar_SMTEncoding_Term.mk_decls_trivial
                                  in
                               FStar_List.append rest uu____12049  in
                             FStar_List.append elts uu____12046  in
                           FStar_List.append uu____12036 uu____12043  in
                         (uu____12035, env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12057,tps,k,uu____12060,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___385_12079  ->
                    match uu___385_12079 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12083 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____12096 = c  in
              match uu____12096 with
              | (name,args,uu____12101,uu____12102,uu____12103) ->
                  let uu____12114 =
                    let uu____12115 =
                      let uu____12127 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____12154  ->
                                match uu____12154 with
                                | (uu____12163,sort,uu____12165) -> sort))
                         in
                      (name, uu____12127, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12115  in
                  [uu____12114]
            else
              (let uu____12176 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____12176 c)
             in
          let inversion_axioms tapp vars =
            let uu____12204 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____12212 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____12212 FStar_Option.isNone))
               in
            if uu____12204
            then []
            else
              (let uu____12247 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____12247 with
               | (xxsym,xx) ->
                   let uu____12260 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____12299  ->
                             fun l  ->
                               match uu____12299 with
                               | (out,decls) ->
                                   let uu____12319 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____12319 with
                                    | (uu____12330,data_t) ->
                                        let uu____12332 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____12332 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____12376 =
                                                 let uu____12377 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____12377.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____12376 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____12380,indices) ->
                                                   indices
                                               | uu____12406 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____12436  ->
                                                         match uu____12436
                                                         with
                                                         | (x,uu____12444) ->
                                                             let uu____12449
                                                               =
                                                               let uu____12450
                                                                 =
                                                                 let uu____12458
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____12458,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____12450
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____12449)
                                                    env)
                                                in
                                             let uu____12463 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____12463 with
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
                                                      let uu____12493 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____12511
                                                                 =
                                                                 let uu____12516
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____12516,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____12511)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____12493
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____12519 =
                                                      let uu____12520 =
                                                        let uu____12525 =
                                                          let uu____12526 =
                                                            let uu____12531 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____12531,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____12526
                                                           in
                                                        (out, uu____12525)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____12520
                                                       in
                                                    (uu____12519,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____12260 with
                    | (data_ax,decls) ->
                        let uu____12544 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____12544 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____12561 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____12561 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____12568 =
                                 let uu____12576 =
                                   let uu____12577 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____12578 =
                                     let uu____12589 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____12602 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____12589,
                                       uu____12602)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____12577 uu____12578
                                    in
                                 let uu____12611 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____12576,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____12611)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____12568
                                in
                             let uu____12617 =
                               FStar_All.pipe_right [fuel_guarded_inversion]
                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                in
                             FStar_List.append decls uu____12617)))
             in
          let uu____12624 =
            let uu____12629 =
              let uu____12630 = FStar_Syntax_Subst.compress k  in
              uu____12630.FStar_Syntax_Syntax.n  in
            match uu____12629 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____12665 -> (tps, k)  in
          (match uu____12624 with
           | (formals,res) ->
               let uu____12672 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____12672 with
                | (formals1,res1) ->
                    let uu____12683 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____12683 with
                     | (vars,guards,env',binder_decls,uu____12708) ->
                         let arity = FStar_List.length vars  in
                         let uu____12722 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____12722 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____12752 =
                                  let uu____12760 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____12760)  in
                                FStar_SMTEncoding_Util.mkApp uu____12752  in
                              let uu____12766 =
                                let tname_decl =
                                  let uu____12776 =
                                    let uu____12777 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____12805  ->
                                              match uu____12805 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____12826 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____12777,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____12826, false)
                                     in
                                  constructor_or_logic_type_decl uu____12776
                                   in
                                let uu____12834 =
                                  match vars with
                                  | [] ->
                                      let uu____12847 =
                                        let uu____12848 =
                                          let uu____12851 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____12851
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____12848
                                         in
                                      ([], uu____12847)
                                  | uu____12863 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____12873 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____12873
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____12889 =
                                          let uu____12897 =
                                            let uu____12898 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____12899 =
                                              let uu____12915 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____12915)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____12898 uu____12899
                                             in
                                          (uu____12897,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____12889
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____12834 with
                                | (tok_decls,env2) ->
                                    let uu____12942 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____12942
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____12766 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____12970 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____12970 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____12992 =
                                               let uu____12993 =
                                                 let uu____13001 =
                                                   let uu____13002 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13002
                                                    in
                                                 (uu____13001,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____12993
                                                in
                                             [uu____12992]
                                           else []  in
                                         let uu____13010 =
                                           let uu____13013 =
                                             let uu____13016 =
                                               let uu____13019 =
                                                 let uu____13020 =
                                                   let uu____13028 =
                                                     let uu____13029 =
                                                       FStar_Ident.range_of_lid
                                                         t
                                                        in
                                                     let uu____13030 =
                                                       let uu____13041 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k1)
                                                          in
                                                       ([[tapp]], vars,
                                                         uu____13041)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____13029
                                                       uu____13030
                                                      in
                                                   (uu____13028,
                                                     FStar_Pervasives_Native.None,
                                                     (Prims.strcat "kinding_"
                                                        ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____13020
                                                  in
                                               [uu____13019]  in
                                             FStar_List.append karr
                                               uu____13016
                                              in
                                           FStar_All.pipe_right uu____13013
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append decls1 uu____13010
                                      in
                                   let aux =
                                     let uu____13060 =
                                       let uu____13063 =
                                         inversion_axioms tapp vars  in
                                       let uu____13066 =
                                         let uu____13069 =
                                           let uu____13072 =
                                             let uu____13073 =
                                               FStar_Ident.range_of_lid t  in
                                             pretype_axiom uu____13073 env2
                                               tapp vars
                                              in
                                           [uu____13072]  in
                                         FStar_All.pipe_right uu____13069
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____13063
                                         uu____13066
                                        in
                                     FStar_List.append kindingAx uu____13060
                                      in
                                   let g =
                                     let uu____13081 =
                                       FStar_All.pipe_right decls
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append uu____13081
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13089,uu____13090,uu____13091,uu____13092,uu____13093)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13101,t,uu____13103,n_tps,uu____13105) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____13115 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____13115 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____13163 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____13163 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____13191 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____13191 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13211 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____13211 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____13290 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____13290,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____13297 =
                                  let uu____13298 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____13298, true)
                                   in
                                let uu____13306 =
                                  let uu____13313 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____13313
                                   in
                                FStar_All.pipe_right uu____13297 uu____13306
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
                              let uu____13325 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____13325 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____13337::uu____13338 ->
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
                                         let uu____13397 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____13398 =
                                           let uu____13409 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____13409)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13397 uu____13398
                                     | uu____13430 -> tok_typing  in
                                   let uu____13441 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____13441 with
                                    | (vars',guards',env'',decls_formals,uu____13466)
                                        ->
                                        let uu____13479 =
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
                                        (match uu____13479 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____13509 ->
                                                   let uu____13518 =
                                                     let uu____13519 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____13519
                                                      in
                                                   [uu____13518]
                                                in
                                             let encode_elim uu____13535 =
                                               let uu____13536 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____13536 with
                                               | (head1,args) ->
                                                   let uu____13587 =
                                                     let uu____13588 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____13588.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____13587 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____13600;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____13601;_},uu____13602)
                                                        ->
                                                        let uu____13607 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____13607
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____13628
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____13628
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
                                                                    uu____13682
                                                                    ->
                                                                    let uu____13683
                                                                    =
                                                                    let uu____13689
                                                                    =
                                                                    let uu____13691
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13691
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13689)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13683
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13711
                                                                    =
                                                                    let uu____13713
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13713
                                                                     in
                                                                    if
                                                                    uu____13711
                                                                    then
                                                                    let uu____13729
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13729]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____13732
                                                                    =
                                                                    let uu____13746
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____13803
                                                                     ->
                                                                    fun
                                                                    uu____13804
                                                                     ->
                                                                    match 
                                                                    (uu____13803,
                                                                    uu____13804)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13915
                                                                    =
                                                                    let uu____13923
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13923
                                                                     in
                                                                    (match uu____13915
                                                                    with
                                                                    | 
                                                                    (uu____13937,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13948
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13948
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13953
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13953
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
                                                                    uu____13746
                                                                     in
                                                                  (match uu____13732
                                                                   with
                                                                   | 
                                                                   (uu____13974,arg_vars,elim_eqns_or_guards,uu____13977)
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
                                                                    let uu____14004
                                                                    =
                                                                    let uu____14012
                                                                    =
                                                                    let uu____14013
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14014
                                                                    =
                                                                    let uu____14025
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14027
                                                                    =
                                                                    let uu____14028
                                                                    =
                                                                    let uu____14033
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14033)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14028
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14025,
                                                                    uu____14027)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14013
                                                                    uu____14014
                                                                     in
                                                                    (uu____14012,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14004
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14048
                                                                    =
                                                                    let uu____14054
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14054,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14048
                                                                     in
                                                                    let uu____14057
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14057
                                                                    then
                                                                    let x =
                                                                    let uu____14066
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14066,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14071
                                                                    =
                                                                    let uu____14079
                                                                    =
                                                                    let uu____14080
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14081
                                                                    =
                                                                    let uu____14092
                                                                    =
                                                                    let uu____14097
                                                                    =
                                                                    let uu____14100
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14100]
                                                                     in
                                                                    [uu____14097]
                                                                     in
                                                                    let uu____14105
                                                                    =
                                                                    let uu____14106
                                                                    =
                                                                    let uu____14111
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14113
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14111,
                                                                    uu____14113)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14106
                                                                     in
                                                                    (uu____14092,
                                                                    [x],
                                                                    uu____14105)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14080
                                                                    uu____14081
                                                                     in
                                                                    let uu____14128
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14079,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14128)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14071
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14139
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
                                                                    (let uu____14177
                                                                    =
                                                                    let uu____14178
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14178
                                                                    dapp1  in
                                                                    [uu____14177])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14139
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14185
                                                                    =
                                                                    let uu____14193
                                                                    =
                                                                    let uu____14194
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14195
                                                                    =
                                                                    let uu____14206
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14208
                                                                    =
                                                                    let uu____14209
                                                                    =
                                                                    let uu____14214
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14214)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14209
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14206,
                                                                    uu____14208)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14194
                                                                    uu____14195
                                                                     in
                                                                    (uu____14193,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14185)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____14232 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14232
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14253
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14253
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
                                                                    uu____14307
                                                                    ->
                                                                    let uu____14308
                                                                    =
                                                                    let uu____14314
                                                                    =
                                                                    let uu____14316
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14316
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14314)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14308
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14336
                                                                    =
                                                                    let uu____14338
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14338
                                                                     in
                                                                    if
                                                                    uu____14336
                                                                    then
                                                                    let uu____14354
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14354]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14357
                                                                    =
                                                                    let uu____14371
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14428
                                                                     ->
                                                                    fun
                                                                    uu____14429
                                                                     ->
                                                                    match 
                                                                    (uu____14428,
                                                                    uu____14429)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14540
                                                                    =
                                                                    let uu____14548
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14548
                                                                     in
                                                                    (match uu____14540
                                                                    with
                                                                    | 
                                                                    (uu____14562,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14573
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14573
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14578
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14578
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
                                                                    uu____14371
                                                                     in
                                                                  (match uu____14357
                                                                   with
                                                                   | 
                                                                   (uu____14599,arg_vars,elim_eqns_or_guards,uu____14602)
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
                                                                    let uu____14629
                                                                    =
                                                                    let uu____14637
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14639
                                                                    =
                                                                    let uu____14650
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14652
                                                                    =
                                                                    let uu____14653
                                                                    =
                                                                    let uu____14658
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14658)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14653
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14650,
                                                                    uu____14652)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14638
                                                                    uu____14639
                                                                     in
                                                                    (uu____14637,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14629
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14673
                                                                    =
                                                                    let uu____14679
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14679,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14673
                                                                     in
                                                                    let uu____14682
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14682
                                                                    then
                                                                    let x =
                                                                    let uu____14691
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14691,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14696
                                                                    =
                                                                    let uu____14704
                                                                    =
                                                                    let uu____14705
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14706
                                                                    =
                                                                    let uu____14717
                                                                    =
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14725
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14725]
                                                                     in
                                                                    [uu____14722]
                                                                     in
                                                                    let uu____14730
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14738
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14736,
                                                                    uu____14738)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14731
                                                                     in
                                                                    (uu____14717,
                                                                    [x],
                                                                    uu____14730)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14705
                                                                    uu____14706
                                                                     in
                                                                    let uu____14753
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14704,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14753)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14696
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14764
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
                                                                    (let uu____14802
                                                                    =
                                                                    let uu____14803
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14803
                                                                    dapp1  in
                                                                    [uu____14802])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14764
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14810
                                                                    =
                                                                    let uu____14818
                                                                    =
                                                                    let uu____14819
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14820
                                                                    =
                                                                    let uu____14831
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14833
                                                                    =
                                                                    let uu____14834
                                                                    =
                                                                    let uu____14839
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14839)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14834
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14831,
                                                                    uu____14833)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14819
                                                                    uu____14820
                                                                     in
                                                                    (uu____14818,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14810)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____14856 ->
                                                        ((let uu____14858 =
                                                            let uu____14864 =
                                                              let uu____14866
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____14868
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____14866
                                                                uu____14868
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____14864)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14858);
                                                         ([], [])))
                                                in
                                             let uu____14876 = encode_elim ()
                                                in
                                             (match uu____14876 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14902 =
                                                      let uu____14905 =
                                                        let uu____14908 =
                                                          let uu____14911 =
                                                            let uu____14914 =
                                                              let uu____14917
                                                                =
                                                                let uu____14920
                                                                  =
                                                                  let uu____14921
                                                                    =
                                                                    let uu____14933
                                                                    =
                                                                    let uu____14934
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14936
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14934
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____14933)
                                                                     in
                                                                  FStar_SMTEncoding_Term.DeclFun
                                                                    uu____14921
                                                                   in
                                                                [uu____14920]
                                                                 in
                                                              FStar_List.append
                                                                uu____14917
                                                                proxy_fresh
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____14914
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          let uu____14947 =
                                                            let uu____14950 =
                                                              let uu____14953
                                                                =
                                                                let uu____14956
                                                                  =
                                                                  let uu____14959
                                                                    =
                                                                    let uu____14962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14967
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14971
                                                                    =
                                                                    let uu____14979
                                                                    =
                                                                    let uu____14980
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14981
                                                                    =
                                                                    let uu____14992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14992)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14980
                                                                    uu____14981
                                                                     in
                                                                    (uu____14979,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14971
                                                                     in
                                                                    let uu____15005
                                                                    =
                                                                    let uu____15008
                                                                    =
                                                                    let uu____15009
                                                                    =
                                                                    let uu____15017
                                                                    =
                                                                    let uu____15018
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15019
                                                                    =
                                                                    let uu____15030
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15032
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15030,
                                                                    uu____15032)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15018
                                                                    uu____15019
                                                                     in
                                                                    (uu____15017,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15009
                                                                     in
                                                                    [uu____15008]
                                                                     in
                                                                    uu____14970
                                                                    ::
                                                                    uu____15005
                                                                     in
                                                                    uu____14962
                                                                    ::
                                                                    uu____14967
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14959
                                                                    elim
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____14956
                                                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                                                 in
                                                              FStar_List.append
                                                                decls_pred
                                                                uu____14953
                                                               in
                                                            FStar_List.append
                                                              decls_formals
                                                              uu____14950
                                                             in
                                                          FStar_List.append
                                                            uu____14911
                                                            uu____14947
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14908
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14905
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14902
                                                     in
                                                  let uu____15049 =
                                                    let uu____15050 =
                                                      FStar_All.pipe_right
                                                        datacons
                                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                                       in
                                                    FStar_List.append
                                                      uu____15050 g
                                                     in
                                                  (uu____15049, env1)))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15084  ->
              fun se  ->
                match uu____15084 with
                | (g,env1) ->
                    let uu____15104 = encode_sigelt env1 se  in
                    (match uu____15104 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15172 =
        match uu____15172 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15209 ->
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
                 ((let uu____15217 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15217
                   then
                     let uu____15222 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15224 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15226 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15222 uu____15224 uu____15226
                   else ());
                  (let uu____15231 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15231 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15249 =
                         let uu____15257 =
                           let uu____15259 =
                             let uu____15261 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15261
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15259  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15257
                          in
                       (match uu____15249 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15281 = FStar_Options.log_queries ()
                                 in
                              if uu____15281
                              then
                                let uu____15284 =
                                  let uu____15286 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15288 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15290 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15286 uu____15288 uu____15290
                                   in
                                FStar_Pervasives_Native.Some uu____15284
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____15306 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____15316 =
                                let uu____15319 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____15319  in
                              FStar_List.append uu____15306 uu____15316  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15331,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15351 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15351 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15372 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15372 with | (uu____15399,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____15415 'Auu____15416 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____15415 *
      'Auu____15416) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15489  ->
              match uu____15489 with
              | (l,uu____15502,uu____15503) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15554  ->
              match uu____15554 with
              | (l,uu____15569,uu____15570) ->
                  let uu____15581 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____15584 =
                    let uu____15587 =
                      let uu____15588 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15588  in
                    [uu____15587]  in
                  uu____15581 :: uu____15584))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15617 =
      let uu____15620 =
        let uu____15621 = FStar_Util.psmap_empty ()  in
        let uu____15636 =
          let uu____15645 = FStar_Util.psmap_empty ()  in (uu____15645, [])
           in
        let uu____15652 =
          let uu____15654 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15654 FStar_Ident.string_of_lid  in
        let uu____15656 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15660 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15621;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15636;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15652;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____15656;
          FStar_SMTEncoding_Env.local_cache = uu____15660
        }  in
      [uu____15620]  in
    FStar_ST.op_Colon_Equals last_env uu____15617
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15704 = FStar_ST.op_Bang last_env  in
      match uu____15704 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15732 ->
          let uu___403_15735 = e  in
          let uu____15736 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___403_15735.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___403_15735.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___403_15735.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___403_15735.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___403_15735.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___403_15735.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___403_15735.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15736;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___403_15735.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___403_15735.FStar_SMTEncoding_Env.global_cache);
            FStar_SMTEncoding_Env.local_cache =
              (uu___403_15735.FStar_SMTEncoding_Env.local_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15744 = FStar_ST.op_Bang last_env  in
    match uu____15744 with
    | [] -> failwith "Empty env stack"
    | uu____15771::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15803  ->
    let uu____15804 = FStar_ST.op_Bang last_env  in
    match uu____15804 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15864  ->
    let uu____15865 = FStar_ST.op_Bang last_env  in
    match uu____15865 with
    | [] -> failwith "Popping an empty stack"
    | uu____15892::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15929  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15982  ->
         let uu____15983 = snapshot_env ()  in
         match uu____15983 with
         | (env_depth,()) ->
             let uu____16005 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16005 with
              | (varops_depth,()) ->
                  let uu____16027 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16027 with
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
        (fun uu____16085  ->
           let uu____16086 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16086 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16181 = snapshot msg  in () 
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
        | (uu____16227::uu____16228,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___404_16236 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___404_16236.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___404_16236.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___404_16236.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16237 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___405_16264 = elt  in
        let uu____16265 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___405_16264.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___405_16264.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____16265;
          FStar_SMTEncoding_Term.a_names =
            (uu___405_16264.FStar_SMTEncoding_Term.a_names)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16285 =
        let uu____16288 =
          let uu____16289 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16289  in
        let uu____16290 = open_fact_db_tags env  in uu____16288 ::
          uu____16290
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16285
  
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
      let uu____16317 = encode_sigelt env se  in
      match uu____16317 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (recover_global_caching_and_update_env :
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
                (let uu____16363 =
                   let uu____16366 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_SMTEncoding_Env.lookup_global_cache env uu____16366
                    in
                 match uu____16363 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None  ->
                     FStar_SMTEncoding_Env.add_to_global_cache env elt)))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____16403 = FStar_Options.log_queries ()  in
        if uu____16403
        then
          let uu____16408 =
            let uu____16409 =
              let uu____16411 =
                let uu____16413 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16413 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16411  in
            FStar_SMTEncoding_Term.Caption uu____16409  in
          uu____16408 :: decls
        else decls  in
      (let uu____16432 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____16432
       then
         let uu____16435 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16435
       else ());
      (let env =
         let uu____16441 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16441 tcenv  in
       let uu____16442 = encode_top_level_facts env se  in
       match uu____16442 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16456 =
               let uu____16459 =
                 let uu____16462 =
                   FStar_All.pipe_right decls
                     (recover_global_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____16462
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____16459  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16456)))
  
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env  ->
    fun name  ->
      fun decls  ->
        let caption decls1 =
          let uu____16495 = FStar_Options.log_queries ()  in
          if uu____16495
          then
            let msg = Prims.strcat "Externals for " name  in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)]  in
        set_env
          (let uu___406_16515 = env  in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___406_16515.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___406_16515.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___406_16515.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___406_16515.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___406_16515.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___406_16515.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___406_16515.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___406_16515.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___406_16515.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___406_16515.FStar_SMTEncoding_Env.global_cache);
             FStar_SMTEncoding_Env.local_cache =
               (uu___406_16515.FStar_SMTEncoding_Env.local_cache)
           });
        (let z3_decls =
           let uu____16520 =
             let uu____16523 =
               FStar_All.pipe_right decls
                 (recover_global_caching_and_update_env env)
                in
             FStar_All.pipe_right uu____16523
               FStar_SMTEncoding_Term.decls_list_of
              in
           caption uu____16520  in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
  
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv  ->
    fun modul  ->
      let uu____16543 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16543
      then ([], [])
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16566 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____16566
          then
            let uu____16569 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16569
          else ());
         (let env =
            let uu____16577 = get_env modul.FStar_Syntax_Syntax.name tcenv
               in
            FStar_All.pipe_right uu____16577
              FStar_SMTEncoding_Env.reset_current_module_fvbs
             in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16616  ->
                    fun se  ->
                      match uu____16616 with
                      | (g,env2) ->
                          let uu____16636 = encode_top_level_facts env2 se
                             in
                          (match uu____16636 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16659 =
            encode_signature
              (let uu___407_16668 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___407_16668.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___407_16668.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___407_16668.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___407_16668.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___407_16668.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___407_16668.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___407_16668.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___407_16668.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___407_16668.FStar_SMTEncoding_Env.encoding_quantifier);
                 FStar_SMTEncoding_Env.global_cache =
                   (uu___407_16668.FStar_SMTEncoding_Env.global_cache);
                 FStar_SMTEncoding_Env.local_cache =
                   (uu___407_16668.FStar_SMTEncoding_Env.local_cache)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16659 with
          | (decls,env1) ->
              (give_decls_to_z3_and_set_env env1 name decls;
               (let uu____16684 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16684
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let uu____16690 =
                  FStar_All.pipe_right env1
                    FStar_SMTEncoding_Env.get_current_module_fvbs
                   in
                (decls, uu____16690)))))
  
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv  ->
    fun name  ->
      fun uu____16718  ->
        match uu____16718 with
        | (decls,fvbs) ->
            ((let uu____16732 =
                (FStar_Options.lax ()) && (FStar_Options.ml_ish ())  in
              if uu____16732
              then ()
              else
                (let uu____16737 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                 if uu____16737
                 then
                   let uu____16740 =
                     FStar_All.pipe_right (FStar_List.length decls)
                       Prims.string_of_int
                      in
                   FStar_Util.print2
                     "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                     name.FStar_Ident.str uu____16740
                 else ()));
             (let env =
                let uu____16748 = get_env name tcenv  in
                FStar_All.pipe_right uu____16748
                  FStar_SMTEncoding_Env.reset_current_module_fvbs
                 in
              let env1 =
                let uu____16750 = FStar_All.pipe_right fvbs FStar_List.rev
                   in
                FStar_All.pipe_right uu____16750
                  (FStar_List.fold_left
                     (fun env1  ->
                        fun fvb  ->
                          FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                            env1) env)
                 in
              give_decls_to_z3_and_set_env env1 name.FStar_Ident.str decls;
              (let uu____16764 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
               if uu____16764
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
        (let uu____16826 =
           let uu____16828 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16828.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16826);
        (let env =
           let uu____16830 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16830 tcenv  in
         let uu____16831 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16870 = aux rest  in
                 (match uu____16870 with
                  | (out,rest1) ->
                      let t =
                        let uu____16898 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16898 with
                        | FStar_Pervasives_Native.Some uu____16901 ->
                            let uu____16902 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16902
                              x.FStar_Syntax_Syntax.sort
                        | uu____16903 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16907 =
                        let uu____16910 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___408_16913 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___408_16913.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___408_16913.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16910 :: out  in
                      (uu____16907, rest1))
             | uu____16918 -> ([], bindings)  in
           let uu____16925 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16925 with
           | (closing,bindings) ->
               let uu____16952 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16952, bindings)
            in
         match uu____16831 with
         | (q1,bindings) ->
             let uu____16983 = encode_env_bindings env bindings  in
             (match uu____16983 with
              | (env_decls,env1) ->
                  ((let uu____17005 =
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
                    if uu____17005
                    then
                      let uu____17012 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17012
                    else ());
                   (let uu____17017 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17017 with
                    | (phi,qdecls) ->
                        let uu____17038 =
                          let uu____17043 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17043 phi
                           in
                        (match uu____17038 with
                         | (labels,phi1) ->
                             let uu____17060 = encode_labels labels  in
                             (match uu____17060 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17097 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17097
                                    then
                                      let uu____17102 =
                                        let uu____17103 =
                                          let uu____17105 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17105
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17103
                                         in
                                      [uu____17102]
                                    else []  in
                                  let query_prelude =
                                    let uu____17113 =
                                      let uu____17114 =
                                        let uu____17115 =
                                          let uu____17118 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____17125 =
                                            let uu____17128 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____17128
                                             in
                                          FStar_List.append uu____17118
                                            uu____17125
                                           in
                                        FStar_List.append env_decls
                                          uu____17115
                                         in
                                      FStar_All.pipe_right uu____17114
                                        (recover_global_caching_and_update_env
                                           env1)
                                       in
                                    FStar_All.pipe_right uu____17113
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____17138 =
                                      let uu____17146 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17147 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17146,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17147)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17138
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
  