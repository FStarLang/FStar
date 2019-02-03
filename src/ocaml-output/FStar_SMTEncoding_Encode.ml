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
                                  (let uu___385_5467 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___385_5467.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___385_5467.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___385_5467.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___385_5467.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___385_5467.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___385_5467.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___385_5467.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___385_5467.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___385_5467.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___385_5467.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___385_5467.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___385_5467.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___385_5467.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___385_5467.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___385_5467.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___385_5467.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___385_5467.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___385_5467.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___385_5467.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___385_5467.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___385_5467.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___385_5467.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___385_5467.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___385_5467.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___385_5467.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___385_5467.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___385_5467.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___385_5467.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___385_5467.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___385_5467.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___385_5467.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___385_5467.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___385_5467.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___385_5467.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___385_5467.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___385_5467.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___385_5467.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___385_5467.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___385_5467.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___385_5467.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___385_5467.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___385_5467.FStar_TypeChecker_Env.nbe)
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
                                             let uu___386_6008 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.encoding_quantifier);
                                               FStar_SMTEncoding_Env.global_cache
                                                 =
                                                 (uu___386_6008.FStar_SMTEncoding_Env.global_cache)
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
    let uu___387_6768 = en  in
    let uu____6769 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___387_6768.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___387_6768.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___387_6768.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___387_6768.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___387_6768.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___387_6768.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___387_6768.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___387_6768.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___387_6768.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___387_6768.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____6769
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____6799  ->
      fun quals  ->
        match uu____6799 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____6904 = FStar_Util.first_N nbinders formals  in
              match uu____6904 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7005  ->
                         fun uu____7006  ->
                           match (uu____7005, uu____7006) with
                           | ((formal,uu____7032),(binder,uu____7034)) ->
                               let uu____7055 =
                                 let uu____7062 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7062)  in
                               FStar_Syntax_Syntax.NT uu____7055) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7076 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7117  ->
                              match uu____7117 with
                              | (x,i) ->
                                  let uu____7136 =
                                    let uu___388_7137 = x  in
                                    let uu____7138 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___388_7137.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___388_7137.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7138
                                    }  in
                                  (uu____7136, i)))
                       in
                    FStar_All.pipe_right uu____7076
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7162 =
                      let uu____7167 = FStar_Syntax_Subst.compress body  in
                      let uu____7168 =
                        let uu____7169 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7169
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7167 uu____7168
                       in
                    uu____7162 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t e =
              let tcenv =
                let uu___389_7225 = env.FStar_SMTEncoding_Env.tcenv  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___389_7225.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___389_7225.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___389_7225.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___389_7225.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___389_7225.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___389_7225.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___389_7225.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___389_7225.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___389_7225.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___389_7225.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___389_7225.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___389_7225.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___389_7225.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___389_7225.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___389_7225.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___389_7225.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___389_7225.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___389_7225.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___389_7225.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___389_7225.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___389_7225.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___389_7225.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___389_7225.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___389_7225.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___389_7225.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___389_7225.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___389_7225.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___389_7225.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___389_7225.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___389_7225.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___389_7225.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___389_7225.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___389_7225.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___389_7225.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___389_7225.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___389_7225.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___389_7225.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___389_7225.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___389_7225.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___389_7225.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___389_7225.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___389_7225.FStar_TypeChecker_Env.nbe)
                }  in
              let subst_comp1 formals actuals comp =
                let subst1 =
                  FStar_List.map2
                    (fun uu____7297  ->
                       fun uu____7298  ->
                         match (uu____7297, uu____7298) with
                         | ((x,uu____7324),(b,uu____7326)) ->
                             let uu____7347 =
                               let uu____7354 =
                                 FStar_Syntax_Syntax.bv_to_name b  in
                               (x, uu____7354)  in
                             FStar_Syntax_Syntax.NT uu____7347) formals
                    actuals
                   in
                FStar_Syntax_Subst.subst_comp subst1 comp  in
              let rec arrow_formals_comp_norm norm1 t1 =
                let t2 =
                  let uu____7379 = FStar_Syntax_Subst.compress t1  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7379
                   in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals,comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____7408 ->
                    let uu____7415 = FStar_Syntax_Util.unrefine t2  in
                    arrow_formals_comp_norm norm1 uu____7415
                | uu____7416 when Prims.op_Negation norm1 ->
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
                | uu____7419 ->
                    let uu____7420 = FStar_Syntax_Syntax.mk_Total t2  in
                    ([], uu____7420)
                 in
              let aux t1 e1 =
                let uu____7462 = FStar_Syntax_Util.abs_formals e1  in
                match uu____7462 with
                | (binders,body,lopt) ->
                    let uu____7494 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____7510 -> arrow_formals_comp_norm false t1  in
                    (match uu____7494 with
                     | (formals,comp) ->
                         let nformals = FStar_List.length formals  in
                         let nbinders = FStar_List.length binders  in
                         let uu____7544 =
                           if nformals < nbinders
                           then
                             let uu____7588 =
                               FStar_Util.first_N nformals binders  in
                             match uu____7588 with
                             | (bs0,rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt  in
                                 let uu____7672 =
                                   subst_comp1 formals bs0 comp  in
                                 (bs0, body1, uu____7672)
                           else
                             if nformals > nbinders
                             then
                               (let uu____7712 =
                                  eta_expand1 binders formals body
                                    (FStar_Syntax_Util.comp_result comp)
                                   in
                                match uu____7712 with
                                | (binders1,body1) ->
                                    let uu____7765 =
                                      subst_comp1 formals binders1 comp  in
                                    (binders1, body1, uu____7765))
                             else
                               (let uu____7778 =
                                  subst_comp1 formals binders comp  in
                                (binders, body, uu____7778))
                            in
                         (match uu____7544 with
                          | (binders1,body1,comp1) ->
                              (binders1, body1, comp1)))
                 in
              let uu____7838 = aux t e  in
              match uu____7838 with
              | (binders,body,comp) ->
                  let uu____7884 =
                    let uu____7895 =
                      FStar_TypeChecker_Env.is_reifiable_comp tcenv comp  in
                    if uu____7895
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv body  in
                      let uu____7910 = aux comp1 body1  in
                      match uu____7910 with
                      | (more_binders,body2,comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp)  in
                  (match uu____7884 with
                   | (binders1,body1,comp1) ->
                       let uu____7993 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None)
                          in
                       (binders1, uu____7993, comp1))
               in
            (try
               (fun uu___391_8020  ->
                  match () with
                  | () ->
                      let uu____8027 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____8027
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____8043 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____8106  ->
                                   fun lb  ->
                                     match uu____8106 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____8161 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____8161
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____8167 =
                                             let uu____8176 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____8176
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____8167 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____8043 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____8306 =
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
                               | uu____8319 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____8329 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____8329 vars)
                                   else
                                     (let uu____8332 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____8332)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____8393;
                                    FStar_Syntax_Syntax.lbeff = uu____8394;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____8396;
                                    FStar_Syntax_Syntax.lbpos = uu____8397;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____8421 =
                                     let uu____8428 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____8428 with
                                     | (tcenv',uu____8444,e_t) ->
                                         let uu____8450 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____8461 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____8450 with
                                          | (e1,t_norm1) ->
                                              ((let uu___392_8478 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___392_8478.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____8421 with
                                    | (env',e1,t_norm1) ->
                                        let uu____8488 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____8488 with
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
                                             ((let uu____8517 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8517
                                               then
                                                 let uu____8522 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8525 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____8522 uu____8525
                                               else ());
                                              (let uu____8530 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8530 with
                                               | (vars,_guards,env'1,binder_decls,uu____8557)
                                                   ->
                                                   let app =
                                                     let uu____8571 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     let uu____8572 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars
                                                        in
                                                     FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                       uu____8571 fvb
                                                       uu____8572
                                                      in
                                                   let uu____8575 =
                                                     let is_logical =
                                                       let uu____8588 =
                                                         let uu____8589 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____8589.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____8588 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____8595 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____8599 =
                                                         let uu____8600 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____8600
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____8599
                                                         (fun lid  ->
                                                            let uu____8609 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____8609
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____8610 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____8610
                                                     then
                                                       let uu____8626 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____8627 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body env'1
                                                          in
                                                       (app, uu____8626,
                                                         uu____8627)
                                                     else
                                                       (let uu____8638 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body env'1
                                                           in
                                                        (app, app,
                                                          uu____8638))
                                                      in
                                                   (match uu____8575 with
                                                    | (pat,app1,(body1,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____8662 =
                                                            let uu____8670 =
                                                              let uu____8671
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8672
                                                                =
                                                                let uu____8683
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____8683)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8671
                                                                uu____8672
                                                               in
                                                            let uu____8692 =
                                                              let uu____8693
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8693
                                                               in
                                                            (uu____8670,
                                                              uu____8692,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8662
                                                           in
                                                        let uu____8699 =
                                                          let uu____8702 =
                                                            let uu____8705 =
                                                              let uu____8708
                                                                =
                                                                let uu____8711
                                                                  =
                                                                  let uu____8714
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1  in
                                                                  eqn ::
                                                                    uu____8714
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____8711
                                                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                                                 in
                                                              FStar_List.append
                                                                decls2
                                                                uu____8708
                                                               in
                                                            FStar_List.append
                                                              binder_decls
                                                              uu____8705
                                                             in
                                                          FStar_List.append
                                                            decls1 uu____8702
                                                           in
                                                        (uu____8699, env2))))))
                               | uu____8723 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____8788 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____8788,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____8794 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____8847  ->
                                         fun fvb  ->
                                           match uu____8847 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____8902 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8902
                                                  in
                                               let gtok =
                                                 let uu____8906 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____8906
                                                  in
                                               let env4 =
                                                 let uu____8909 =
                                                   let uu____8912 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____8912
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____8909
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____8794 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____9037
                                     t_norm uu____9039 =
                                     match (uu____9037, uu____9039) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____9069;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____9070;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____9072;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____9073;_})
                                         ->
                                         let uu____9100 =
                                           let uu____9107 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____9107 with
                                           | (tcenv',uu____9123,e_t) ->
                                               let uu____9129 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____9140 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____9129 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___393_9157 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___393_9157.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____9100 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____9170 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____9170
                                                then
                                                  let uu____9175 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____9177 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____9179 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____9175 uu____9177
                                                    uu____9179
                                                else ());
                                               (let uu____9184 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____9184 with
                                                | (binders,body,tres_comp) ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders)
                                                       in
                                                    let uu____9211 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp
                                                       in
                                                    (match uu____9211 with
                                                     | (pre_opt,tres) ->
                                                         ((let uu____9233 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify")
                                                              in
                                                           if uu____9233
                                                           then
                                                             let uu____9238 =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn
                                                                in
                                                             let uu____9240 =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders
                                                                in
                                                             let uu____9243 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body
                                                                in
                                                             let uu____9245 =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp
                                                                in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____9238
                                                               uu____9240
                                                               uu____9243
                                                               uu____9245
                                                           else ());
                                                          (let uu____9250 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env'
                                                              in
                                                           match uu____9250
                                                           with
                                                           | (vars,guards,env'1,binder_decls,uu____9279)
                                                               ->
                                                               let uu____9292
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                     ->
                                                                    let uu____9305
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards
                                                                     in
                                                                    (uu____9305,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____9309
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1
                                                                     in
                                                                    (match uu____9309
                                                                    with
                                                                    | 
                                                                    (guard,decls0)
                                                                    ->
                                                                    let uu____9322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard])
                                                                     in
                                                                    (uu____9322,
                                                                    decls0))
                                                                  in
                                                               (match uu____9292
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
                                                                    let uu____9343
                                                                    =
                                                                    let uu____9355
                                                                    =
                                                                    let uu____9358
                                                                    =
                                                                    let uu____9361
                                                                    =
                                                                    let uu____9364
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars  in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____9364
                                                                     in
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    uu____9361
                                                                     in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____9358
                                                                     in
                                                                    (g,
                                                                    uu____9355,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____9343
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
                                                                    let uu____9395
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____9395
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
                                                                    let uu____9410
                                                                    =
                                                                    let uu____9413
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    uu____9413
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9410
                                                                     in
                                                                    let gmax
                                                                    =
                                                                    let uu____9419
                                                                    =
                                                                    let uu____9422
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    uu____9422
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9419
                                                                     in
                                                                    let uu____9427
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1  in
                                                                    (match uu____9427
                                                                    with
                                                                    | 
                                                                    (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____9443
                                                                    =
                                                                    let uu____9451
                                                                    =
                                                                    let uu____9452
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9453
                                                                    =
                                                                    let uu____9469
                                                                    =
                                                                    let uu____9470
                                                                    =
                                                                    let uu____9475
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    (guard,
                                                                    uu____9475)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____9470
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9469)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____9452
                                                                    uu____9453
                                                                     in
                                                                    let uu____9489
                                                                    =
                                                                    let uu____9490
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9490
                                                                     in
                                                                    (uu____9451,
                                                                    uu____9489,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9443
                                                                     in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____9497
                                                                    =
                                                                    let uu____9505
                                                                    =
                                                                    let uu____9506
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9507
                                                                    =
                                                                    let uu____9518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____9518)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9506
                                                                    uu____9507
                                                                     in
                                                                    (uu____9505,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9497
                                                                     in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____9532
                                                                    =
                                                                    let uu____9540
                                                                    =
                                                                    let uu____9541
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9542
                                                                    =
                                                                    let uu____9553
                                                                    =
                                                                    let uu____9554
                                                                    =
                                                                    let uu____9559
                                                                    =
                                                                    let uu____9560
                                                                    =
                                                                    let uu____9563
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____9563
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    mk_g_app
                                                                    uu____9560
                                                                     in
                                                                    (gsapp,
                                                                    uu____9559)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____9554
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9553)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9541
                                                                    uu____9542
                                                                     in
                                                                    (uu____9540,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9532
                                                                     in
                                                                    let uu____9577
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
                                                                    let uu____9589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____9589
                                                                    (fuel ::
                                                                    vars)  in
                                                                    let uu____9591
                                                                    =
                                                                    let uu____9599
                                                                    =
                                                                    let uu____9600
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9601
                                                                    =
                                                                    let uu____9612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9612)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9600
                                                                    uu____9601
                                                                     in
                                                                    (uu____9599,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9591
                                                                     in
                                                                    let uu____9625
                                                                    =
                                                                    let uu____9634
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp  in
                                                                    match uu____9634
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____9649
                                                                    =
                                                                    let uu____9652
                                                                    =
                                                                    let uu____9653
                                                                    =
                                                                    let uu____9661
                                                                    =
                                                                    let uu____9662
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____9663
                                                                    =
                                                                    let uu____9674
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing)
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____9674)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____9662
                                                                    uu____9663
                                                                     in
                                                                    (uu____9661,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____9653
                                                                     in
                                                                    [uu____9652]
                                                                     in
                                                                    (d3,
                                                                    uu____9649)
                                                                     in
                                                                    match uu____9625
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))
                                                                     in
                                                                    (match uu____9577
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
                                                                    ->
                                                                    let uu____9731
                                                                    =
                                                                    let uu____9734
                                                                    =
                                                                    let uu____9737
                                                                    =
                                                                    let uu____9740
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____9740
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____9737
                                                                     in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____9734
                                                                     in
                                                                    let uu____9747
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                                                     in
                                                                    (uu____9731,
                                                                    uu____9747,
                                                                    env02))))))))))
                                      in
                                   let uu____9752 =
                                     let uu____9765 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____9828  ->
                                          fun uu____9829  ->
                                            match (uu____9828, uu____9829)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____9954 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____9954 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____9765
                                      in
                                   (match uu____9752 with
                                    | (decls2,eqns,env01) ->
                                        let uu____10021 =
                                          let isDeclFun uu___376_10034 =
                                            match uu___376_10034 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10036 -> true
                                            | uu____10049 -> false  in
                                          let uu____10051 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____10051
                                            (fun decls3  ->
                                               let uu____10076 =
                                                 FStar_List.fold_left
                                                   (fun uu____10100  ->
                                                      fun elt  ->
                                                        match uu____10100
                                                        with
                                                        | (prefix_decls,rest)
                                                            ->
                                                            let uu____10128 =
                                                              FStar_List.partition
                                                                isDeclFun
                                                                elt.FStar_SMTEncoding_Term.decls
                                                               in
                                                            (match uu____10128
                                                             with
                                                             | (elt_decl_funs,elt_rest)
                                                                 ->
                                                                 ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                   (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___394_10160
                                                                    = elt  in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___394_10160.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.args_sorts
                                                                    =
                                                                    (uu___394_10160.FStar_SMTEncoding_Term.args_sorts);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___394_10160.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___394_10160.FStar_SMTEncoding_Term.a_names);
                                                                    FStar_SMTEncoding_Term.aux_decls
                                                                    =
                                                                    (uu___394_10160.FStar_SMTEncoding_Term.aux_decls)
                                                                    })]))))
                                                   ([], []) decls3
                                                  in
                                               match uu____10076 with
                                               | (prefix_decls,rest) ->
                                                   let uu____10181 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial
                                                      in
                                                   (uu____10181, rest))
                                           in
                                        (match uu____10021 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____10203 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___377_10209  ->
                                        match uu___377_10209 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____10212 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____10220 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____10220)))
                                in
                             if uu____10203
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___396_10242  ->
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
                   let uu____10281 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____10281
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 let uu____10300 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 (uu____10300, env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____10356 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____10356 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____10362 = encode_sigelt' env se  in
      match uu____10362 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____10374 =
                  let uu____10377 =
                    let uu____10378 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____10378  in
                  [uu____10377]  in
                FStar_All.pipe_right uu____10374
                  FStar_SMTEncoding_Term.mk_decls_trivial
            | uu____10383 ->
                let uu____10384 =
                  let uu____10387 =
                    let uu____10390 =
                      let uu____10391 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____10391  in
                    [uu____10390]  in
                  FStar_All.pipe_right uu____10387
                    FStar_SMTEncoding_Term.mk_decls_trivial
                   in
                let uu____10398 =
                  let uu____10401 =
                    let uu____10404 =
                      let uu____10407 =
                        let uu____10408 =
                          FStar_Util.format1 "</end encoding %s>" nm  in
                        FStar_SMTEncoding_Term.Caption uu____10408  in
                      [uu____10407]  in
                    FStar_All.pipe_right uu____10404
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append g uu____10401  in
                FStar_List.append uu____10384 uu____10398
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
        let uu____10428 =
          let uu____10429 = FStar_Syntax_Subst.compress t  in
          uu____10429.FStar_Syntax_Syntax.n  in
        match uu____10428 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10434)) -> s = "opaque_to_smt"
        | uu____10439 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____10448 =
          let uu____10449 = FStar_Syntax_Subst.compress t  in
          uu____10449.FStar_Syntax_Syntax.n  in
        match uu____10448 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____10454)) -> s = "uninterpreted_by_smt"
        | uu____10459 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10465 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____10471 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____10483 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____10484 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10485 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____10498 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____10500 =
            let uu____10502 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____10502  in
          if uu____10500
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____10531 ->
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
               let uu____10563 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____10563 with
               | (formals,uu____10583) ->
                   let arity = FStar_List.length formals  in
                   let uu____10607 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____10607 with
                    | (aname,atok,env2) ->
                        let uu____10633 =
                          let uu____10638 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____10638 env2
                           in
                        (match uu____10633 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____10650 =
                                 let uu____10651 =
                                   let uu____10663 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____10683  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____10663,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____10651
                                  in
                               [uu____10650;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____10700 =
                               let aux uu____10761 uu____10762 =
                                 match (uu____10761, uu____10762) with
                                 | ((bv,uu____10821),(env3,acc_sorts,acc)) ->
                                     let uu____10868 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____10868 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____10700 with
                              | (uu____10952,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____10978 =
                                      let uu____10986 =
                                        let uu____10987 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____10988 =
                                          let uu____10999 =
                                            let uu____11000 =
                                              let uu____11005 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____11005)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____11000
                                             in
                                          ([[app]], xs_sorts, uu____10999)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____10987 uu____10988
                                         in
                                      (uu____10986,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____10978
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
                                    let uu____11022 =
                                      let uu____11030 =
                                        let uu____11031 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11032 =
                                          let uu____11043 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____11043)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11031 uu____11032
                                         in
                                      (uu____11030,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11022
                                     in
                                  let uu____11056 =
                                    let uu____11059 =
                                      FStar_All.pipe_right
                                        (FStar_List.append a_decls
                                           [a_eq; tok_correspondence])
                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                       in
                                    FStar_List.append decls uu____11059  in
                                  (env2, uu____11056))))
                in
             let uu____11068 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____11068 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11094,uu____11095)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____11096 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____11096 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____11118,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____11125 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___378_11131  ->
                      match uu___378_11131 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____11134 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____11140 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____11143 -> false))
               in
            Prims.op_Negation uu____11125  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____11153 =
               let uu____11158 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____11158 env fv t quals  in
             match uu____11153 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____11173 =
                   let uu____11174 =
                     let uu____11177 =
                       primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                         lid tname tsym
                        in
                     FStar_All.pipe_right uu____11177
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   FStar_List.append decls uu____11174  in
                 (uu____11173, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____11187 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____11187 with
           | (uvs,f1) ->
               let env1 =
                 let uu___397_11199 = env  in
                 let uu____11200 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___397_11199.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___397_11199.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___397_11199.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____11200;
                   FStar_SMTEncoding_Env.warn =
                     (uu___397_11199.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___397_11199.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___397_11199.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___397_11199.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___397_11199.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___397_11199.FStar_SMTEncoding_Env.encoding_quantifier);
                   FStar_SMTEncoding_Env.global_cache =
                     (uu___397_11199.FStar_SMTEncoding_Env.global_cache)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____11202 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____11202 with
                | (f3,decls) ->
                    let g =
                      let uu____11216 =
                        let uu____11219 =
                          let uu____11220 =
                            let uu____11228 =
                              let uu____11229 =
                                let uu____11231 =
                                  FStar_Syntax_Print.lid_to_string l  in
                                FStar_Util.format1 "Assumption: %s"
                                  uu____11231
                                 in
                              FStar_Pervasives_Native.Some uu____11229  in
                            let uu____11235 =
                              FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                (Prims.strcat "assumption_" l.FStar_Ident.str)
                               in
                            (f3, uu____11228, uu____11235)  in
                          FStar_SMTEncoding_Util.mkAssume uu____11220  in
                        [uu____11219]  in
                      FStar_All.pipe_right uu____11216
                        FStar_SMTEncoding_Term.mk_decls_trivial
                       in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____11244) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____11258 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____11280 =
                       let uu____11283 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____11283.FStar_Syntax_Syntax.fv_name  in
                     uu____11280.FStar_Syntax_Syntax.v  in
                   let uu____11284 =
                     let uu____11286 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____11286  in
                   if uu____11284
                   then
                     let val_decl =
                       let uu___398_11318 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___398_11318.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___398_11318.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___398_11318.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____11319 = encode_sigelt' env1 val_decl  in
                     match uu____11319 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____11258 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____11355,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____11357;
                          FStar_Syntax_Syntax.lbtyp = uu____11358;
                          FStar_Syntax_Syntax.lbeff = uu____11359;
                          FStar_Syntax_Syntax.lbdef = uu____11360;
                          FStar_Syntax_Syntax.lbattrs = uu____11361;
                          FStar_Syntax_Syntax.lbpos = uu____11362;_}::[]),uu____11363)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____11382 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____11382 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____11425 =
                   let uu____11428 =
                     let uu____11429 =
                       let uu____11437 =
                         let uu____11438 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____11439 =
                           let uu____11450 =
                             let uu____11451 =
                               let uu____11456 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____11456)  in
                             FStar_SMTEncoding_Util.mkEq uu____11451  in
                           ([[b2t_x]], [xx], uu____11450)  in
                         FStar_SMTEncoding_Term.mkForall uu____11438
                           uu____11439
                          in
                       (uu____11437,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11429  in
                   [uu____11428]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____11425
                  in
               let uu____11488 =
                 FStar_All.pipe_right decls
                   FStar_SMTEncoding_Term.mk_decls_trivial
                  in
               (uu____11488, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____11491,uu____11492) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___379_11502  ->
                  match uu___379_11502 with
                  | FStar_Syntax_Syntax.Discriminator uu____11504 -> true
                  | uu____11506 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____11508,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____11520 =
                     let uu____11522 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____11522.FStar_Ident.idText  in
                   uu____11520 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___380_11529  ->
                     match uu___380_11529 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____11532 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____11535) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___381_11549  ->
                  match uu___381_11549 with
                  | FStar_Syntax_Syntax.Projector uu____11551 -> true
                  | uu____11557 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____11561 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____11561 with
           | FStar_Pervasives_Native.Some uu____11568 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___399_11570 = se  in
                 let uu____11571 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____11571;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___399_11570.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___399_11570.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___399_11570.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____11574) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11589) ->
          let uu____11598 = encode_sigelts env ses  in
          (match uu____11598 with
           | (g,env1) ->
               let uu____11609 =
                 FStar_List.fold_left
                   (fun uu____11633  ->
                      fun elt  ->
                        match uu____11633 with
                        | (g',inversions) ->
                            let uu____11661 =
                              FStar_All.pipe_right
                                elt.FStar_SMTEncoding_Term.decls
                                (FStar_List.partition
                                   (fun uu___382_11684  ->
                                      match uu___382_11684 with
                                      | FStar_SMTEncoding_Term.Assume
                                          {
                                            FStar_SMTEncoding_Term.assumption_term
                                              = uu____11686;
                                            FStar_SMTEncoding_Term.assumption_caption
                                              = FStar_Pervasives_Native.Some
                                              "inversion axiom";
                                            FStar_SMTEncoding_Term.assumption_name
                                              = uu____11687;
                                            FStar_SMTEncoding_Term.assumption_fact_ids
                                              = uu____11688;_}
                                          -> false
                                      | uu____11695 -> true))
                               in
                            (match uu____11661 with
                             | (elt_g',elt_inversions) ->
                                 ((FStar_List.append g'
                                     [(let uu___400_11720 = elt  in
                                       {
                                         FStar_SMTEncoding_Term.sym_name =
                                           (uu___400_11720.FStar_SMTEncoding_Term.sym_name);
                                         FStar_SMTEncoding_Term.args_sorts =
                                           (uu___400_11720.FStar_SMTEncoding_Term.args_sorts);
                                         FStar_SMTEncoding_Term.key =
                                           (uu___400_11720.FStar_SMTEncoding_Term.key);
                                         FStar_SMTEncoding_Term.decls =
                                           elt_g';
                                         FStar_SMTEncoding_Term.a_names =
                                           (uu___400_11720.FStar_SMTEncoding_Term.a_names);
                                         FStar_SMTEncoding_Term.aux_decls =
                                           (uu___400_11720.FStar_SMTEncoding_Term.aux_decls)
                                       })]),
                                   (FStar_List.append inversions
                                      elt_inversions)))) ([], []) g
                  in
               (match uu____11609 with
                | (g',inversions) ->
                    let uu____11739 =
                      FStar_List.fold_left
                        (fun uu____11763  ->
                           fun elt  ->
                             match uu____11763 with
                             | (decls,rest) ->
                                 let uu____11791 =
                                   FStar_All.pipe_right
                                     elt.FStar_SMTEncoding_Term.decls
                                     (FStar_List.partition
                                        (fun uu___383_11812  ->
                                           match uu___383_11812 with
                                           | FStar_SMTEncoding_Term.DeclFun
                                               uu____11814 -> true
                                           | uu____11827 -> false))
                                    in
                                 (match uu____11791 with
                                  | (elt_decls,elt_rest) ->
                                      ((FStar_List.append decls elt_decls),
                                        (FStar_List.append rest
                                           [(let uu___401_11852 = elt  in
                                             {
                                               FStar_SMTEncoding_Term.sym_name
                                                 =
                                                 (uu___401_11852.FStar_SMTEncoding_Term.sym_name);
                                               FStar_SMTEncoding_Term.args_sorts
                                                 =
                                                 (uu___401_11852.FStar_SMTEncoding_Term.args_sorts);
                                               FStar_SMTEncoding_Term.key =
                                                 (uu___401_11852.FStar_SMTEncoding_Term.key);
                                               FStar_SMTEncoding_Term.decls =
                                                 elt_rest;
                                               FStar_SMTEncoding_Term.a_names
                                                 =
                                                 (uu___401_11852.FStar_SMTEncoding_Term.a_names);
                                               FStar_SMTEncoding_Term.aux_decls
                                                 =
                                                 (uu___401_11852.FStar_SMTEncoding_Term.aux_decls)
                                             })])))) ([], []) g'
                       in
                    (match uu____11739 with
                     | (decls,rest) ->
                         let uu____11871 =
                           let uu____11872 =
                             FStar_All.pipe_right decls
                               FStar_SMTEncoding_Term.mk_decls_trivial
                              in
                           let uu____11879 =
                             let uu____11882 =
                               FStar_All.pipe_right inversions
                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                in
                             FStar_List.append rest uu____11882  in
                           FStar_List.append uu____11872 uu____11879  in
                         (uu____11871, env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____11890,tps,k,uu____11893,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___384_11912  ->
                    match uu___384_11912 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11916 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____11929 = c  in
              match uu____11929 with
              | (name,args,uu____11934,uu____11935,uu____11936) ->
                  let uu____11947 =
                    let uu____11948 =
                      let uu____11960 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____11987  ->
                                match uu____11987 with
                                | (uu____11996,sort,uu____11998) -> sort))
                         in
                      (name, uu____11960, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____11948  in
                  [uu____11947]
            else
              (let uu____12009 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____12009 c)
             in
          let inversion_axioms tapp vars =
            let uu____12037 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____12045 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____12045 FStar_Option.isNone))
               in
            if uu____12037
            then []
            else
              (let uu____12080 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____12080 with
               | (xxsym,xx) ->
                   let uu____12093 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____12132  ->
                             fun l  ->
                               match uu____12132 with
                               | (out,decls) ->
                                   let uu____12152 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____12152 with
                                    | (uu____12163,data_t) ->
                                        let uu____12165 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____12165 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____12209 =
                                                 let uu____12210 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____12210.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____12209 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____12213,indices) ->
                                                   indices
                                               | uu____12239 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____12269  ->
                                                         match uu____12269
                                                         with
                                                         | (x,uu____12277) ->
                                                             let uu____12282
                                                               =
                                                               let uu____12283
                                                                 =
                                                                 let uu____12291
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____12291,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____12283
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____12282)
                                                    env)
                                                in
                                             let uu____12296 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____12296 with
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
                                                      let uu____12326 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____12344
                                                                 =
                                                                 let uu____12349
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____12349,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____12344)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____12326
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____12352 =
                                                      let uu____12353 =
                                                        let uu____12358 =
                                                          let uu____12359 =
                                                            let uu____12364 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____12364,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____12359
                                                           in
                                                        (out, uu____12358)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____12353
                                                       in
                                                    (uu____12352,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____12093 with
                    | (data_ax,decls) ->
                        let uu____12377 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____12377 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____12394 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____12394 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____12401 =
                                 let uu____12409 =
                                   let uu____12410 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____12411 =
                                     let uu____12422 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____12435 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____12422,
                                       uu____12435)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____12410 uu____12411
                                    in
                                 let uu____12444 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____12409,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____12444)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____12401
                                in
                             let uu____12450 =
                               FStar_All.pipe_right [fuel_guarded_inversion]
                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                in
                             FStar_List.append decls uu____12450)))
             in
          let uu____12457 =
            let uu____12462 =
              let uu____12463 = FStar_Syntax_Subst.compress k  in
              uu____12463.FStar_Syntax_Syntax.n  in
            match uu____12462 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____12498 -> (tps, k)  in
          (match uu____12457 with
           | (formals,res) ->
               let uu____12505 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____12505 with
                | (formals1,res1) ->
                    let uu____12516 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____12516 with
                     | (vars,guards,env',binder_decls,uu____12541) ->
                         let arity = FStar_List.length vars  in
                         let uu____12555 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____12555 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____12585 =
                                  let uu____12593 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____12593)  in
                                FStar_SMTEncoding_Util.mkApp uu____12585  in
                              let uu____12599 =
                                let tname_decl =
                                  let uu____12609 =
                                    let uu____12610 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____12638  ->
                                              match uu____12638 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____12659 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____12610,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____12659, false)
                                     in
                                  constructor_or_logic_type_decl uu____12609
                                   in
                                let uu____12667 =
                                  match vars with
                                  | [] ->
                                      let uu____12680 =
                                        let uu____12681 =
                                          let uu____12684 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____12684
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____12681
                                         in
                                      ([], uu____12680)
                                  | uu____12696 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____12706 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____12706
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____12722 =
                                          let uu____12730 =
                                            let uu____12731 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____12732 =
                                              let uu____12748 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____12748)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____12731 uu____12732
                                             in
                                          (uu____12730,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____12722
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____12667 with
                                | (tok_decls,env2) ->
                                    let uu____12775 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____12775
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____12599 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____12803 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____12803 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____12825 =
                                               let uu____12826 =
                                                 let uu____12834 =
                                                   let uu____12835 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____12835
                                                    in
                                                 (uu____12834,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____12826
                                                in
                                             [uu____12825]
                                           else []  in
                                         let uu____12843 =
                                           let uu____12846 =
                                             let uu____12849 =
                                               let uu____12852 =
                                                 let uu____12853 =
                                                   let uu____12861 =
                                                     let uu____12862 =
                                                       FStar_Ident.range_of_lid
                                                         t
                                                        in
                                                     let uu____12863 =
                                                       let uu____12874 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k1)
                                                          in
                                                       ([[tapp]], vars,
                                                         uu____12874)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____12862
                                                       uu____12863
                                                      in
                                                   (uu____12861,
                                                     FStar_Pervasives_Native.None,
                                                     (Prims.strcat "kinding_"
                                                        ttok))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____12853
                                                  in
                                               [uu____12852]  in
                                             FStar_List.append karr
                                               uu____12849
                                              in
                                           FStar_All.pipe_right uu____12846
                                             FStar_SMTEncoding_Term.mk_decls_trivial
                                            in
                                         FStar_List.append decls1 uu____12843
                                      in
                                   let aux =
                                     let uu____12893 =
                                       let uu____12896 =
                                         inversion_axioms tapp vars  in
                                       let uu____12899 =
                                         let uu____12902 =
                                           let uu____12905 =
                                             let uu____12906 =
                                               FStar_Ident.range_of_lid t  in
                                             pretype_axiom uu____12906 env2
                                               tapp vars
                                              in
                                           [uu____12905]  in
                                         FStar_All.pipe_right uu____12902
                                           FStar_SMTEncoding_Term.mk_decls_trivial
                                          in
                                       FStar_List.append uu____12896
                                         uu____12899
                                        in
                                     FStar_List.append kindingAx uu____12893
                                      in
                                   let g =
                                     let uu____12914 =
                                       FStar_All.pipe_right decls
                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                        in
                                     FStar_List.append uu____12914
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____12922,uu____12923,uu____12924,uu____12925,uu____12926)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____12934,t,uu____12936,n_tps,uu____12938) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____12948 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____12948 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____12996 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____12996 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____13024 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____13024 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13044 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____13044 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____13123 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____13123,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____13130 =
                                  let uu____13131 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____13131, true)
                                   in
                                let uu____13139 =
                                  let uu____13146 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____13146
                                   in
                                FStar_All.pipe_right uu____13130 uu____13139
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
                              let uu____13158 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____13158 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____13170::uu____13171 ->
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
                                         let uu____13230 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____13231 =
                                           let uu____13242 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____13242)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13230 uu____13231
                                     | uu____13263 -> tok_typing  in
                                   let uu____13274 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____13274 with
                                    | (vars',guards',env'',decls_formals,uu____13299)
                                        ->
                                        let uu____13312 =
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
                                        (match uu____13312 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____13342 ->
                                                   let uu____13351 =
                                                     let uu____13352 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____13352
                                                      in
                                                   [uu____13351]
                                                in
                                             let encode_elim uu____13368 =
                                               let uu____13369 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____13369 with
                                               | (head1,args) ->
                                                   let uu____13420 =
                                                     let uu____13421 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____13421.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____13420 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____13433;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____13434;_},uu____13435)
                                                        ->
                                                        let uu____13440 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____13440
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____13461
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____13461
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
                                                                    uu____13515
                                                                    ->
                                                                    let uu____13516
                                                                    =
                                                                    let uu____13522
                                                                    =
                                                                    let uu____13524
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____13524
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____13522)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____13516
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____13544
                                                                    =
                                                                    let uu____13546
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____13546
                                                                     in
                                                                    if
                                                                    uu____13544
                                                                    then
                                                                    let uu____13562
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____13562]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____13565
                                                                    =
                                                                    let uu____13579
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____13636
                                                                     ->
                                                                    fun
                                                                    uu____13637
                                                                     ->
                                                                    match 
                                                                    (uu____13636,
                                                                    uu____13637)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____13748
                                                                    =
                                                                    let uu____13756
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____13756
                                                                     in
                                                                    (match uu____13748
                                                                    with
                                                                    | 
                                                                    (uu____13770,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____13781
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____13781
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____13786
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____13786
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
                                                                    uu____13579
                                                                     in
                                                                  (match uu____13565
                                                                   with
                                                                   | 
                                                                   (uu____13807,arg_vars,elim_eqns_or_guards,uu____13810)
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
                                                                    let uu____13837
                                                                    =
                                                                    let uu____13845
                                                                    =
                                                                    let uu____13846
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13847
                                                                    =
                                                                    let uu____13858
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____13860
                                                                    =
                                                                    let uu____13861
                                                                    =
                                                                    let uu____13866
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____13866)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13861
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____13858,
                                                                    uu____13860)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13846
                                                                    uu____13847
                                                                     in
                                                                    (uu____13845,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13837
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____13881
                                                                    =
                                                                    let uu____13887
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____13887,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____13881
                                                                     in
                                                                    let uu____13890
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____13890
                                                                    then
                                                                    let x =
                                                                    let uu____13899
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____13899,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____13904
                                                                    =
                                                                    let uu____13912
                                                                    =
                                                                    let uu____13913
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____13914
                                                                    =
                                                                    let uu____13925
                                                                    =
                                                                    let uu____13930
                                                                    =
                                                                    let uu____13933
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____13933]
                                                                     in
                                                                    [uu____13930]
                                                                     in
                                                                    let uu____13938
                                                                    =
                                                                    let uu____13939
                                                                    =
                                                                    let uu____13944
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____13946
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____13944,
                                                                    uu____13946)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13939
                                                                     in
                                                                    (uu____13925,
                                                                    [x],
                                                                    uu____13938)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____13913
                                                                    uu____13914
                                                                     in
                                                                    let uu____13961
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____13912,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____13961)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13904
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____13972
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
                                                                    (let uu____14010
                                                                    =
                                                                    let uu____14011
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14011
                                                                    dapp1  in
                                                                    [uu____14010])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____13972
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14018
                                                                    =
                                                                    let uu____14026
                                                                    =
                                                                    let uu____14027
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14028
                                                                    =
                                                                    let uu____14039
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14041
                                                                    =
                                                                    let uu____14042
                                                                    =
                                                                    let uu____14047
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14047)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14042
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14039,
                                                                    uu____14041)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14027
                                                                    uu____14028
                                                                     in
                                                                    (uu____14026,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14018)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____14065 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14065
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14086
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14086
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
                                                                    uu____14140
                                                                    ->
                                                                    let uu____14141
                                                                    =
                                                                    let uu____14147
                                                                    =
                                                                    let uu____14149
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14149
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14147)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14141
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14169
                                                                    =
                                                                    let uu____14171
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14171
                                                                     in
                                                                    if
                                                                    uu____14169
                                                                    then
                                                                    let uu____14187
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14187]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14190
                                                                    =
                                                                    let uu____14204
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14261
                                                                     ->
                                                                    fun
                                                                    uu____14262
                                                                     ->
                                                                    match 
                                                                    (uu____14261,
                                                                    uu____14262)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14373
                                                                    =
                                                                    let uu____14381
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14381
                                                                     in
                                                                    (match uu____14373
                                                                    with
                                                                    | 
                                                                    (uu____14395,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14406
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14406
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14411
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14411
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
                                                                    uu____14204
                                                                     in
                                                                  (match uu____14190
                                                                   with
                                                                   | 
                                                                   (uu____14432,arg_vars,elim_eqns_or_guards,uu____14435)
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
                                                                    let uu____14462
                                                                    =
                                                                    let uu____14470
                                                                    =
                                                                    let uu____14471
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14472
                                                                    =
                                                                    let uu____14483
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14485
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    let uu____14491
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14491)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14486
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14483,
                                                                    uu____14485)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14471
                                                                    uu____14472
                                                                     in
                                                                    (uu____14470,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14462
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14506
                                                                    =
                                                                    let uu____14512
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14512,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14506
                                                                     in
                                                                    let uu____14515
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14515
                                                                    then
                                                                    let x =
                                                                    let uu____14524
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14524,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14529
                                                                    =
                                                                    let uu____14537
                                                                    =
                                                                    let uu____14538
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14539
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    let uu____14555
                                                                    =
                                                                    let uu____14558
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14558]
                                                                     in
                                                                    [uu____14555]
                                                                     in
                                                                    let uu____14563
                                                                    =
                                                                    let uu____14564
                                                                    =
                                                                    let uu____14569
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14571
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14569,
                                                                    uu____14571)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14564
                                                                     in
                                                                    (uu____14550,
                                                                    [x],
                                                                    uu____14563)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14538
                                                                    uu____14539
                                                                     in
                                                                    let uu____14586
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14537,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14586)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14529
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14597
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
                                                                    (let uu____14635
                                                                    =
                                                                    let uu____14636
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14636
                                                                    dapp1  in
                                                                    [uu____14635])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14597
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14643
                                                                    =
                                                                    let uu____14651
                                                                    =
                                                                    let uu____14652
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14653
                                                                    =
                                                                    let uu____14664
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14666
                                                                    =
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14672
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14672)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14667
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14664,
                                                                    uu____14666)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14652
                                                                    uu____14653
                                                                     in
                                                                    (uu____14651,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14643)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____14689 ->
                                                        ((let uu____14691 =
                                                            let uu____14697 =
                                                              let uu____14699
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____14701
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____14699
                                                                uu____14701
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____14697)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14691);
                                                         ([], [])))
                                                in
                                             let uu____14709 = encode_elim ()
                                                in
                                             (match uu____14709 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14735 =
                                                      let uu____14738 =
                                                        let uu____14741 =
                                                          let uu____14744 =
                                                            let uu____14747 =
                                                              let uu____14750
                                                                =
                                                                let uu____14753
                                                                  =
                                                                  let uu____14754
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    let uu____14767
                                                                    =
                                                                    let uu____14769
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14769
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14767
                                                                     in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____14766)
                                                                     in
                                                                  FStar_SMTEncoding_Term.DeclFun
                                                                    uu____14754
                                                                   in
                                                                [uu____14753]
                                                                 in
                                                              FStar_List.append
                                                                uu____14750
                                                                proxy_fresh
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____14747
                                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                                             in
                                                          let uu____14780 =
                                                            let uu____14783 =
                                                              let uu____14786
                                                                =
                                                                let uu____14789
                                                                  =
                                                                  let uu____14792
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____14800
                                                                    =
                                                                    let uu____14803
                                                                    =
                                                                    let uu____14804
                                                                    =
                                                                    let uu____14812
                                                                    =
                                                                    let uu____14813
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14814
                                                                    =
                                                                    let uu____14825
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14825)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14813
                                                                    uu____14814
                                                                     in
                                                                    (uu____14812,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14804
                                                                     in
                                                                    let uu____14838
                                                                    =
                                                                    let uu____14841
                                                                    =
                                                                    let uu____14842
                                                                    =
                                                                    let uu____14850
                                                                    =
                                                                    let uu____14851
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14852
                                                                    =
                                                                    let uu____14863
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14865
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14863,
                                                                    uu____14865)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14851
                                                                    uu____14852
                                                                     in
                                                                    (uu____14850,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14842
                                                                     in
                                                                    [uu____14841]
                                                                     in
                                                                    uu____14803
                                                                    ::
                                                                    uu____14838
                                                                     in
                                                                    uu____14795
                                                                    ::
                                                                    uu____14800
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14792
                                                                    elim
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____14789
                                                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                                                 in
                                                              FStar_List.append
                                                                decls_pred
                                                                uu____14786
                                                               in
                                                            FStar_List.append
                                                              decls_formals
                                                              uu____14783
                                                             in
                                                          FStar_List.append
                                                            uu____14744
                                                            uu____14780
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14741
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14738
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14735
                                                     in
                                                  let uu____14882 =
                                                    let uu____14883 =
                                                      FStar_All.pipe_right
                                                        datacons
                                                        FStar_SMTEncoding_Term.mk_decls_trivial
                                                       in
                                                    FStar_List.append
                                                      uu____14883 g
                                                     in
                                                  (uu____14882, env1)))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14917  ->
              fun se  ->
                match uu____14917 with
                | (g,env1) ->
                    let uu____14937 = encode_sigelt env1 se  in
                    (match uu____14937 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15005 =
        match uu____15005 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15042 ->
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
                 ((let uu____15050 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15050
                   then
                     let uu____15055 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15057 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15059 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15055 uu____15057 uu____15059
                   else ());
                  (let uu____15064 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15064 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15082 =
                         let uu____15090 =
                           let uu____15092 =
                             let uu____15094 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15094
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15092  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15090
                          in
                       (match uu____15082 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15114 = FStar_Options.log_queries ()
                                 in
                              if uu____15114
                              then
                                let uu____15117 =
                                  let uu____15119 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15121 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15123 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15119 uu____15121 uu____15123
                                   in
                                FStar_Pervasives_Native.Some uu____15117
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              let uu____15139 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                                 in
                              let uu____15149 =
                                let uu____15152 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial
                                   in
                                FStar_List.append decls' uu____15152  in
                              FStar_List.append uu____15139 uu____15149  in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15164,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15184 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15184 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15205 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15205 with | (uu____15232,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____15248 'Auu____15249 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____15248 *
      'Auu____15249) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15322  ->
              match uu____15322 with
              | (l,uu____15335,uu____15336) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15387  ->
              match uu____15387 with
              | (l,uu____15402,uu____15403) ->
                  let uu____15414 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____15417 =
                    let uu____15420 =
                      let uu____15421 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____15421  in
                    [uu____15420]  in
                  uu____15414 :: uu____15417))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____15450 =
      let uu____15453 =
        let uu____15454 = FStar_Util.psmap_empty ()  in
        let uu____15469 = FStar_Util.psmap_empty ()  in
        let uu____15472 =
          let uu____15474 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15474 FStar_Ident.string_of_lid  in
        let uu____15476 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15454;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15469;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15472;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____15476
        }  in
      [uu____15453]  in
    FStar_ST.op_Colon_Equals last_env uu____15450
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____15520 = FStar_ST.op_Bang last_env  in
      match uu____15520 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15548 ->
          let uu___402_15551 = e  in
          let uu____15552 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___402_15551.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___402_15551.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___402_15551.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___402_15551.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___402_15551.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___402_15551.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___402_15551.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15552;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___402_15551.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___402_15551.FStar_SMTEncoding_Env.global_cache)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____15560 = FStar_ST.op_Bang last_env  in
    match uu____15560 with
    | [] -> failwith "Empty env stack"
    | uu____15587::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____15619  ->
    let uu____15620 = FStar_ST.op_Bang last_env  in
    match uu____15620 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____15680  ->
    let uu____15681 = FStar_ST.op_Bang last_env  in
    match uu____15681 with
    | [] -> failwith "Popping an empty stack"
    | uu____15708::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15745  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____15798  ->
         let uu____15799 = snapshot_env ()  in
         match uu____15799 with
         | (env_depth,()) ->
             let uu____15821 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____15821 with
              | (varops_depth,()) ->
                  let uu____15843 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____15843 with
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
        (fun uu____15901  ->
           let uu____15902 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____15902 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____15997 = snapshot msg  in () 
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
        | (uu____16043::uu____16044,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___403_16052 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___403_16052.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___403_16052.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___403_16052.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16053 -> d
  
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun elt  ->
        let uu___404_16080 = elt  in
        let uu____16081 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids))
           in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___404_16080.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.args_sorts =
            (uu___404_16080.FStar_SMTEncoding_Term.args_sorts);
          FStar_SMTEncoding_Term.key =
            (uu___404_16080.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____16081;
          FStar_SMTEncoding_Term.a_names =
            (uu___404_16080.FStar_SMTEncoding_Term.a_names);
          FStar_SMTEncoding_Term.aux_decls =
            (uu___404_16080.FStar_SMTEncoding_Term.aux_decls)
        }
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16101 =
        let uu____16104 =
          let uu____16105 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16105  in
        let uu____16106 = open_fact_db_tags env  in uu____16104 ::
          uu____16106
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16101
  
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
      let uu____16133 = encode_sigelt env se  in
      match uu____16133 with
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
                (let uu____16179 =
                   let uu____16182 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must
                      in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____16182
                    in
                 match uu____16179 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     if
                       cache_elt.FStar_SMTEncoding_Term.sym_name =
                         (FStar_Pervasives_Native.Some "")
                     then []
                     else
                       (let uu____16202 =
                          FStar_List.fold_left
                            (fun uu____16226  ->
                               fun srt  ->
                                 match uu____16226 with
                                 | (names1,terms) ->
                                     let uu____16258 =
                                       FStar_SMTEncoding_Env.fresh_fvar "x"
                                         srt
                                        in
                                     FStar_All.pipe_right uu____16258
                                       (fun uu____16282  ->
                                          match uu____16282 with
                                          | (n1,t) ->
                                              ((FStar_List.append names1 [n1]),
                                                (FStar_List.append terms [t]))))
                            ([], [])
                            cache_elt.FStar_SMTEncoding_Term.args_sorts
                           in
                        match uu____16202 with
                        | (names1,terms) ->
                            let d =
                              let uu____16330 =
                                let uu____16349 =
                                  FStar_All.pipe_right
                                    elt.FStar_SMTEncoding_Term.sym_name
                                    FStar_Util.must
                                   in
                                let uu____16356 =
                                  FStar_List.zip names1
                                    cache_elt.FStar_SMTEncoding_Term.args_sorts
                                   in
                                let uu____16365 =
                                  let uu____16366 =
                                    let uu____16374 =
                                      FStar_All.pipe_right
                                        cache_elt.FStar_SMTEncoding_Term.sym_name
                                        FStar_Util.must
                                       in
                                    (uu____16374, terms)  in
                                  FStar_SMTEncoding_Util.mkApp uu____16366
                                   in
                                (uu____16349, uu____16356,
                                  FStar_SMTEncoding_Term.Term_sort,
                                  uu____16365, FStar_Pervasives_Native.None)
                                 in
                              FStar_SMTEncoding_Term.mkDefineFun uu____16330
                               in
                            FStar_All.pipe_right
                              [d;
                              FStar_SMTEncoding_Term.RetainAssumptions
                                (cache_elt.FStar_SMTEncoding_Term.a_names)]
                              FStar_SMTEncoding_Term.mk_decls_trivial)
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____16398 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must
                          in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____16398
                         elt);
                      [elt]))))
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____16428 = FStar_Options.log_queries ()  in
        if uu____16428
        then
          let uu____16433 =
            let uu____16434 =
              let uu____16436 =
                let uu____16438 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16438 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16436  in
            FStar_SMTEncoding_Term.Caption uu____16434  in
          uu____16433 :: decls
        else decls  in
      (let uu____16457 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
       if uu____16457
       then
         let uu____16460 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16460
       else ());
      (let env =
         let uu____16466 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16466 tcenv  in
       let uu____16467 = encode_top_level_facts env se  in
       match uu____16467 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16481 =
               let uu____16484 =
                 let uu____16487 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1)
                    in
                 FStar_All.pipe_right uu____16487
                   FStar_SMTEncoding_Term.decls_list_of
                  in
               caption uu____16484  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16481)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16501 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16501
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16516 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
          if uu____16516
          then
            let uu____16519 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16519
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____16565  ->
                    fun se  ->
                      match uu____16565 with
                      | (g,env2) ->
                          let uu____16585 = encode_top_level_facts env2 se
                             in
                          (match uu____16585 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____16608 =
            encode_signature
              (let uu___405_16617 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___405_16617.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___405_16617.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___405_16617.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___405_16617.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___405_16617.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___405_16617.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___405_16617.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___405_16617.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___405_16617.FStar_SMTEncoding_Env.encoding_quantifier);
                 FStar_SMTEncoding_Env.global_cache =
                   (uu___405_16617.FStar_SMTEncoding_Env.global_cache)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____16608 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____16637 = FStar_Options.log_queries ()  in
                if uu____16637
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
                 (let uu___406_16657 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___406_16657.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___406_16657.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___406_16657.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___406_16657.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___406_16657.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___406_16657.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___406_16657.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___406_16657.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___406_16657.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___406_16657.FStar_SMTEncoding_Env.global_cache)
                  });
               (let uu____16660 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium  in
                if uu____16660
                then
                  FStar_Util.print1 "Done encoding externals for %s\n" name
                else ());
               (let decls1 =
                  let uu____16669 =
                    let uu____16672 =
                      FStar_All.pipe_right decls
                        (recover_caching_and_update_env env1)
                       in
                    FStar_All.pipe_right uu____16672
                      FStar_SMTEncoding_Term.decls_list_of
                     in
                  caption uu____16669  in
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
        (let uu____16731 =
           let uu____16733 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16733.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16731);
        (let env =
           let uu____16735 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16735 tcenv  in
         let uu____16736 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____16775 = aux rest  in
                 (match uu____16775 with
                  | (out,rest1) ->
                      let t =
                        let uu____16803 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16803 with
                        | FStar_Pervasives_Native.Some uu____16806 ->
                            let uu____16807 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16807
                              x.FStar_Syntax_Syntax.sort
                        | uu____16808 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____16812 =
                        let uu____16815 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___407_16818 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___407_16818.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___407_16818.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16815 :: out  in
                      (uu____16812, rest1))
             | uu____16823 -> ([], bindings)  in
           let uu____16830 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____16830 with
           | (closing,bindings) ->
               let uu____16857 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16857, bindings)
            in
         match uu____16736 with
         | (q1,bindings) ->
             let uu____16888 = encode_env_bindings env bindings  in
             (match uu____16888 with
              | (env_decls,env1) ->
                  ((let uu____16910 =
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
                    if uu____16910
                    then
                      let uu____16917 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16917
                    else ());
                   (let uu____16922 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____16922 with
                    | (phi,qdecls) ->
                        let uu____16943 =
                          let uu____16948 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16948 phi
                           in
                        (match uu____16943 with
                         | (labels,phi1) ->
                             let uu____16965 = encode_labels labels  in
                             (match uu____16965 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17002 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17002
                                    then
                                      let uu____17007 =
                                        let uu____17008 =
                                          let uu____17010 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17010
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17008
                                         in
                                      [uu____17007]
                                    else []  in
                                  let query_prelude =
                                    let uu____17018 =
                                      let uu____17019 =
                                        let uu____17020 =
                                          let uu____17023 =
                                            FStar_All.pipe_right label_prefix
                                              FStar_SMTEncoding_Term.mk_decls_trivial
                                             in
                                          let uu____17030 =
                                            let uu____17033 =
                                              FStar_All.pipe_right caption
                                                FStar_SMTEncoding_Term.mk_decls_trivial
                                               in
                                            FStar_List.append qdecls
                                              uu____17033
                                             in
                                          FStar_List.append uu____17023
                                            uu____17030
                                           in
                                        FStar_List.append env_decls
                                          uu____17020
                                         in
                                      FStar_All.pipe_right uu____17019
                                        (recover_caching_and_update_env env1)
                                       in
                                    FStar_All.pipe_right uu____17018
                                      FStar_SMTEncoding_Term.decls_list_of
                                     in
                                  let qry =
                                    let uu____17043 =
                                      let uu____17051 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17052 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17051,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17052)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17043
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
  