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
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.decl Prims.list *
            FStar_SMTEncoding_Env.env_t))
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let wrap f env s t =
    let uu____2734 = f env.FStar_SMTEncoding_Env.tcenv s t  in
    (uu____2734, env)  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____2754 =
      let uu____2755 =
        let uu____2763 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2763, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2755  in
    let uu____2768 =
      let uu____2771 =
        let uu____2772 =
          let uu____2780 =
            let uu____2781 =
              let uu____2792 =
                let uu____2793 =
                  let uu____2798 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2798)  in
                FStar_SMTEncoding_Util.mkImp uu____2793  in
              ([[typing_pred]], [xx], uu____2792)  in
            let uu____2817 =
              let uu____2832 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2832  in
            uu____2817 uu____2781  in
          (uu____2780, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2772  in
      [uu____2771]  in
    uu____2754 :: uu____2768  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2865 =
      let uu____2866 =
        let uu____2874 =
          let uu____2875 = FStar_TypeChecker_Env.get_range env  in
          let uu____2876 =
            let uu____2887 =
              let uu____2892 =
                let uu____2895 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2895]  in
              [uu____2892]  in
            let uu____2900 =
              let uu____2901 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2901 tt  in
            (uu____2887, [bb], uu____2900)  in
          FStar_SMTEncoding_Term.mkForall uu____2875 uu____2876  in
        (uu____2874, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2866  in
    let uu____2920 =
      let uu____2923 =
        let uu____2924 =
          let uu____2932 =
            let uu____2933 =
              let uu____2944 =
                let uu____2945 =
                  let uu____2950 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2950)  in
                FStar_SMTEncoding_Util.mkImp uu____2945  in
              ([[typing_pred]], [xx], uu____2944)  in
            let uu____2971 =
              let uu____2986 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2986  in
            uu____2971 uu____2933  in
          (uu____2932, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2924  in
      [uu____2923]  in
    uu____2865 :: uu____2920  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3010 =
        let uu____3016 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____3016, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____3010  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3040 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3040  in
    let uu____3045 =
      let uu____3046 =
        let uu____3054 =
          let uu____3055 = FStar_TypeChecker_Env.get_range env  in
          let uu____3056 =
            let uu____3067 =
              let uu____3072 =
                let uu____3075 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3075]  in
              [uu____3072]  in
            let uu____3080 =
              let uu____3081 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3081 tt  in
            (uu____3067, [bb], uu____3080)  in
          FStar_SMTEncoding_Term.mkForall uu____3055 uu____3056  in
        (uu____3054, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3046  in
    let uu____3100 =
      let uu____3103 =
        let uu____3104 =
          let uu____3112 =
            let uu____3113 =
              let uu____3124 =
                let uu____3125 =
                  let uu____3130 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3130)  in
                FStar_SMTEncoding_Util.mkImp uu____3125  in
              ([[typing_pred]], [xx], uu____3124)  in
            let uu____3151 =
              let uu____3166 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3166  in
            uu____3151 uu____3113  in
          (uu____3112, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3104  in
      let uu____3171 =
        let uu____3174 =
          let uu____3175 =
            let uu____3183 =
              let uu____3184 =
                let uu____3195 =
                  let uu____3196 =
                    let uu____3201 =
                      let uu____3202 =
                        let uu____3205 =
                          let uu____3208 =
                            let uu____3211 =
                              let uu____3212 =
                                let uu____3217 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3218 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3217, uu____3218)  in
                              FStar_SMTEncoding_Util.mkGT uu____3212  in
                            let uu____3220 =
                              let uu____3223 =
                                let uu____3224 =
                                  let uu____3229 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3230 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3229, uu____3230)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3224  in
                              let uu____3232 =
                                let uu____3235 =
                                  let uu____3236 =
                                    let uu____3241 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3242 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3241, uu____3242)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3236  in
                                [uu____3235]  in
                              uu____3223 :: uu____3232  in
                            uu____3211 :: uu____3220  in
                          typing_pred_y :: uu____3208  in
                        typing_pred :: uu____3205  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3202  in
                    (uu____3201, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3196  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3195)
                 in
              let uu____3266 =
                let uu____3281 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3281  in
              uu____3266 uu____3184  in
            (uu____3183,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3175  in
        [uu____3174]  in
      uu____3103 :: uu____3171  in
    uu____3045 :: uu____3100  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3314 =
      let uu____3315 =
        let uu____3323 =
          let uu____3324 = FStar_TypeChecker_Env.get_range env  in
          let uu____3325 =
            let uu____3336 =
              let uu____3341 =
                let uu____3344 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3344]  in
              [uu____3341]  in
            let uu____3349 =
              let uu____3350 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3350 tt  in
            (uu____3336, [bb], uu____3349)  in
          FStar_SMTEncoding_Term.mkForall uu____3324 uu____3325  in
        (uu____3323, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3315  in
    let uu____3369 =
      let uu____3372 =
        let uu____3373 =
          let uu____3381 =
            let uu____3382 =
              let uu____3393 =
                let uu____3394 =
                  let uu____3399 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3399)  in
                FStar_SMTEncoding_Util.mkImp uu____3394  in
              ([[typing_pred]], [xx], uu____3393)  in
            let uu____3420 =
              let uu____3435 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3435  in
            uu____3420 uu____3382  in
          (uu____3381, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3373  in
      [uu____3372]  in
    uu____3314 :: uu____3369  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3463 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3463]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3491 =
      let uu____3492 =
        let uu____3500 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3500, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3492  in
    [uu____3491]  in
  let mk_macro_name s = Prims.strcat FStar_Ident.reserved_prefix s  in
  let bind_macro env lid macro_name =
    let fvb = FStar_SMTEncoding_Env.lookup_lid env lid  in
    FStar_SMTEncoding_Env.push_free_var env lid
      fvb.FStar_SMTEncoding_Env.smt_arity macro_name
      fvb.FStar_SMTEncoding_Env.smt_token
     in
  let mk_and_interp env conj uu____3553 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let macro_name = mk_macro_name conj  in
    let macro =
      let uu____3595 =
        let uu____3614 =
          let uu____3615 =
            let uu____3623 =
              let uu____3626 =
                let uu____3629 =
                  FStar_SMTEncoding_Util.mkITE
                    (valid_a, b, FStar_SMTEncoding_Term.mk_Witness_term)
                   in
                [uu____3629]  in
              a :: uu____3626  in
            (conj, uu____3623)  in
          FStar_SMTEncoding_Util.mkApp uu____3615  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____3614,
          (FStar_Pervasives_Native.Some "macro for embedded conjunction"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____3595  in
    let uu____3658 =
      let uu____3659 =
        let uu____3660 =
          let uu____3668 =
            let uu____3669 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____3670 =
              let uu____3681 =
                let uu____3682 =
                  let uu____3687 =
                    FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                  (uu____3687, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____3682  in
              ([[l_and_a_b]], [aa; bb], uu____3681)  in
            FStar_SMTEncoding_Term.mkForall uu____3669 uu____3670  in
          (uu____3668, (FStar_Pervasives_Native.Some "/\\ interpretation"),
            "l_and-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3660  in
      [uu____3659; macro]  in
    let uu____3715 = bind_macro env FStar_Parser_Const.and_lid macro_name  in
    (uu____3658, uu____3715)  in
  let mk_or_interp env disj uu____3736 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let macro_name = mk_macro_name disj  in
    let macro =
      let uu____3778 =
        let uu____3797 =
          let uu____3798 =
            let uu____3806 =
              let uu____3809 =
                let uu____3812 =
                  let uu____3813 =
                    let uu____3820 = FStar_SMTEncoding_Util.mkNot valid_a  in
                    (uu____3820, b, FStar_SMTEncoding_Term.mk_Witness_term)
                     in
                  FStar_SMTEncoding_Util.mkITE uu____3813  in
                [uu____3812]  in
              a :: uu____3809  in
            (disj, uu____3806)  in
          FStar_SMTEncoding_Util.mkApp uu____3798  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____3797,
          (FStar_Pervasives_Native.Some "macro for embedded disjunction"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____3778  in
    let uu____3849 =
      let uu____3850 =
        let uu____3851 =
          let uu____3859 =
            let uu____3860 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____3861 =
              let uu____3872 =
                let uu____3873 =
                  let uu____3878 =
                    FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                  (uu____3878, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____3873  in
              ([[l_or_a_b]], [aa; bb], uu____3872)  in
            FStar_SMTEncoding_Term.mkForall uu____3860 uu____3861  in
          (uu____3859, (FStar_Pervasives_Native.Some "\\/ interpretation"),
            "l_or-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3851  in
      [uu____3850; macro]  in
    let uu____3906 = bind_macro env FStar_Parser_Const.or_lid macro_name  in
    (uu____3849, uu____3906)  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let macro_name = mk_macro_name imp  in
    let macro =
      let uu____3969 =
        let uu____3988 =
          let uu____3989 =
            let uu____3997 =
              let uu____4000 =
                let uu____4003 =
                  FStar_SMTEncoding_Util.mkITE
                    (valid_a, b, FStar_SMTEncoding_Term.mk_Witness_term)
                   in
                [uu____4003]  in
              a :: uu____4000  in
            (imp, uu____3997)  in
          FStar_SMTEncoding_Util.mkApp uu____3989  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____3988,
          (FStar_Pervasives_Native.Some "macro for embedded implication"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____3969  in
    let uu____4032 =
      let uu____4033 =
        let uu____4034 =
          let uu____4042 =
            let uu____4043 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4044 =
              let uu____4055 =
                let uu____4056 =
                  let uu____4061 =
                    FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                  (uu____4061, valid)  in
                FStar_SMTEncoding_Util.mkIff uu____4056  in
              ([[l_imp_a_b]], [aa; bb], uu____4055)  in
            FStar_SMTEncoding_Term.mkForall uu____4043 uu____4044  in
          (uu____4042, (FStar_Pervasives_Native.Some "==> interpretation"),
            "l_imp-interp")
           in
        FStar_SMTEncoding_Util.mkAssume uu____4034  in
      [uu____4033; macro]  in
    let uu____4089 = bind_macro env FStar_Parser_Const.imp_lid macro_name  in
    (uu____4032, uu____4089)  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____4145 =
      let uu____4146 =
        let uu____4154 =
          let uu____4155 = FStar_TypeChecker_Env.get_range env  in
          let uu____4156 =
            let uu____4167 =
              let uu____4168 =
                let uu____4173 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____4173, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4168  in
            ([[l_iff_a_b]], [aa; bb], uu____4167)  in
          FStar_SMTEncoding_Term.mkForall uu____4155 uu____4156  in
        (uu____4154, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4146  in
    [uu____4145]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4238 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4238  in
    let uu____4243 =
      let uu____4244 =
        let uu____4252 =
          let uu____4253 = FStar_TypeChecker_Env.get_range env  in
          let uu____4254 =
            let uu____4265 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4265)  in
          FStar_SMTEncoding_Term.mkForall uu____4253 uu____4254  in
        (uu____4252, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4244  in
    [uu____4243]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____4342 =
      let uu____4343 =
        let uu____4351 =
          let uu____4352 = FStar_TypeChecker_Env.get_range env  in
          let uu____4353 =
            let uu____4364 =
              let uu____4365 =
                let uu____4370 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4370, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4365  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4364)  in
          FStar_SMTEncoding_Term.mkForall uu____4352 uu____4353  in
        (uu____4351, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4343  in
    [uu____4342]  in
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
    let uu____4466 =
      let uu____4467 =
        let uu____4475 =
          let uu____4476 = FStar_TypeChecker_Env.get_range env  in
          let uu____4477 =
            let uu____4488 =
              let uu____4489 =
                let uu____4494 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4494, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4489  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4488)  in
          FStar_SMTEncoding_Term.mkForall uu____4476 uu____4477  in
        (uu____4475, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4467  in
    [uu____4466]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4554 =
      let uu____4555 =
        let uu____4563 =
          let uu____4564 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4564 range_ty  in
        let uu____4565 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4563, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4565)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4555  in
    [uu____4554]  in
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
        let uu____4619 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4619 x1 t  in
      let uu____4621 = FStar_TypeChecker_Env.get_range env  in
      let uu____4622 =
        let uu____4633 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4633)  in
      FStar_SMTEncoding_Term.mkForall uu____4621 uu____4622  in
    let uu____4652 =
      let uu____4653 =
        let uu____4661 =
          let uu____4662 = FStar_TypeChecker_Env.get_range env  in
          let uu____4663 =
            let uu____4674 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4674)  in
          FStar_SMTEncoding_Term.mkForall uu____4662 uu____4663  in
        (uu____4661,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4653  in
    [uu____4652]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4737 =
      let uu____4738 =
        let uu____4746 =
          let uu____4747 = FStar_TypeChecker_Env.get_range env  in
          let uu____4748 =
            let uu____4764 =
              let uu____4765 =
                let uu____4770 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4771 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4770, uu____4771)  in
              FStar_SMTEncoding_Util.mkAnd uu____4765  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4764)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4747 uu____4748  in
        (uu____4746,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4738  in
    [uu____4737]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, (wrap mk_unit));
    (FStar_Parser_Const.bool_lid, (wrap mk_bool));
    (FStar_Parser_Const.int_lid, (wrap mk_int));
    (FStar_Parser_Const.string_lid, (wrap mk_str));
    (FStar_Parser_Const.true_lid, (wrap mk_true_interp));
    (FStar_Parser_Const.false_lid, (wrap mk_false_interp));
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, (wrap mk_iff_interp));
    (FStar_Parser_Const.not_lid, (wrap mk_not_interp));
    (FStar_Parser_Const.eq2_lid, (wrap mk_eq2_interp));
    (FStar_Parser_Const.eq3_lid, (wrap mk_eq3_interp));
    (FStar_Parser_Const.range_lid, (wrap mk_range_interp));
    (FStar_Parser_Const.inversion_lid, (wrap mk_inversion_axiom));
    (FStar_Parser_Const.with_type_lid, (wrap mk_with_type_axiom))]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____5428 =
            FStar_Util.find_opt
              (fun uu____5474  ->
                 match uu____5474 with
                 | (l,uu____5494) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5428 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____5555,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5628 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5628 with
        | (form,decls) ->
            let uu____5637 =
              let uu____5640 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5640]  in
            FStar_List.append decls uu____5637
  
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
              let uu____5697 =
                ((let uu____5701 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5701) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5697
              then
                let arg_sorts =
                  let uu____5715 =
                    let uu____5716 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5716.FStar_Syntax_Syntax.n  in
                  match uu____5715 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5722) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5760  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5767 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5769 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5769 with
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
                (let uu____5811 = prims.is lid  in
                 if uu____5811
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5822 = prims.mk lid vname  in
                   match uu____5822 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____5856 =
                      let uu____5875 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____5875 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____5903 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____5903
                            then
                              let uu____5908 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___380_5911 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___380_5911.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___380_5911.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___380_5911.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___380_5911.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___380_5911.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___380_5911.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___380_5911.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___380_5911.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___380_5911.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___380_5911.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___380_5911.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___380_5911.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___380_5911.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___380_5911.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___380_5911.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___380_5911.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___380_5911.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___380_5911.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___380_5911.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___380_5911.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___380_5911.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___380_5911.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___380_5911.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___380_5911.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___380_5911.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___380_5911.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___380_5911.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___380_5911.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___380_5911.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___380_5911.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___380_5911.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___380_5911.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___380_5911.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___380_5911.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___380_5911.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___380_5911.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___380_5911.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___380_5911.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___380_5911.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___380_5911.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___380_5911.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___380_5911.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____5908
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____5934 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____5934)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____5856 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6015 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6015 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6049 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___370_6110  ->
                                       match uu___370_6110 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6114 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6114 with
                                            | (uu____6138,(xxsym,uu____6140))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6164 =
                                                  let uu____6165 =
                                                    let uu____6173 =
                                                      let uu____6174 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6175 =
                                                        let uu____6186 =
                                                          let uu____6187 =
                                                            let uu____6192 =
                                                              let uu____6193
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6193
                                                               in
                                                            (vapp,
                                                              uu____6192)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6187
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6186)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6174 uu____6175
                                                       in
                                                    (uu____6173,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6165
                                                   in
                                                [uu____6164])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6208 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6208 with
                                            | (uu____6232,(xxsym,uu____6234))
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
                                                let uu____6266 =
                                                  let uu____6267 =
                                                    let uu____6275 =
                                                      let uu____6276 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6277 =
                                                        let uu____6288 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6288)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6276 uu____6277
                                                       in
                                                    (uu____6275,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6267
                                                   in
                                                [uu____6266])
                                       | uu____6301 -> []))
                                in
                             let uu____6302 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6302 with
                              | (vars,guards,env',decls1,uu____6329) ->
                                  let uu____6342 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6355 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6355, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6359 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6359 with
                                         | (g,ds) ->
                                             let uu____6372 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6372,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6342 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6389 =
                                           let uu____6397 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6397)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6389
                                          in
                                       let uu____6403 =
                                         let vname_decl =
                                           let uu____6411 =
                                             let uu____6423 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6443  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6423,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6411
                                            in
                                         let uu____6454 =
                                           let env2 =
                                             let uu___381_6460 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___381_6460.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____6461 =
                                             let uu____6463 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6463  in
                                           if uu____6461
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6454 with
                                         | (tok_typing,decls2) ->
                                             let uu____6480 =
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
                                                   let uu____6504 =
                                                     let uu____6505 =
                                                       let uu____6508 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6508
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6505
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6504)
                                               | uu____6518 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6533 =
                                                       let uu____6541 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6541]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6533
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6563 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6564 =
                                                       let uu____6575 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6575)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6563 uu____6564
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6585 =
                                                       let uu____6593 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6593,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6585
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
                                                       let uu____6632 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6633 =
                                                         let uu____6644 =
                                                           let uu____6645 =
                                                             let uu____6650 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6651 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6650,
                                                               uu____6651)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6645
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6644)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6632
                                                         uu____6633
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
                                             (match uu____6480 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6403 with
                                        | (decls2,env2) ->
                                            let uu____6702 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____6712 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____6712 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____6727 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____6727,
                                                    decls)
                                               in
                                            (match uu____6702 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____6744 =
                                                     let uu____6752 =
                                                       let uu____6753 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6754 =
                                                         let uu____6765 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____6765)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6753
                                                         uu____6754
                                                        in
                                                     (uu____6752,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____6744
                                                    in
                                                 let freshness =
                                                   let uu____6781 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____6781
                                                   then
                                                     let uu____6789 =
                                                       let uu____6790 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6791 =
                                                         let uu____6804 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____6822 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____6804,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____6822)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____6790
                                                         uu____6791
                                                        in
                                                     let uu____6828 =
                                                       let uu____6831 =
                                                         let uu____6832 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____6832 env2
                                                           vapp vars
                                                          in
                                                       [uu____6831]  in
                                                     uu____6789 :: uu____6828
                                                   else []  in
                                                 let g =
                                                   let uu____6838 =
                                                     let uu____6841 =
                                                       let uu____6844 =
                                                         let uu____6847 =
                                                           let uu____6850 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____6850
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____6847
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____6844
                                                        in
                                                     FStar_List.append decls2
                                                       uu____6841
                                                      in
                                                   FStar_List.append decls11
                                                     uu____6838
                                                    in
                                                 (g, env2))))))))
  
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
          let uu____6892 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____6892 with
          | FStar_Pervasives_Native.None  ->
              let uu____6903 = encode_free_var false env x t t_norm []  in
              (match uu____6903 with
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
            let uu____6974 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____6974 with
            | (decls,env1) ->
                let uu____6993 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____6993
                then
                  let uu____7002 =
                    let uu____7005 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7005  in
                  (uu____7002, env1)
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
             (fun uu____7065  ->
                fun lb  ->
                  match uu____7065 with
                  | (decls,env1) ->
                      let uu____7085 =
                        let uu____7092 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7092
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7085 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7125 = FStar_Syntax_Util.head_and_args t  in
    match uu____7125 with
    | (hd1,args) ->
        let uu____7169 =
          let uu____7170 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7170.FStar_Syntax_Syntax.n  in
        (match uu____7169 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7176,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7200 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7211 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___382_7219 = en  in
    let uu____7220 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___382_7219.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___382_7219.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___382_7219.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___382_7219.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___382_7219.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7220;
      FStar_SMTEncoding_Env.nolabels =
        (uu___382_7219.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___382_7219.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___382_7219.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___382_7219.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___382_7219.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7252  ->
      fun quals  ->
        match uu____7252 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7359 = FStar_Util.first_N nbinders formals  in
              match uu____7359 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7460  ->
                         fun uu____7461  ->
                           match (uu____7460, uu____7461) with
                           | ((formal,uu____7487),(binder,uu____7489)) ->
                               let uu____7510 =
                                 let uu____7517 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7517)  in
                               FStar_Syntax_Syntax.NT uu____7510) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7531 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7572  ->
                              match uu____7572 with
                              | (x,i) ->
                                  let uu____7591 =
                                    let uu___383_7592 = x  in
                                    let uu____7593 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_7592.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_7592.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7593
                                    }  in
                                  (uu____7591, i)))
                       in
                    FStar_All.pipe_right uu____7531
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7617 =
                      let uu____7622 = FStar_Syntax_Subst.compress body  in
                      let uu____7623 =
                        let uu____7624 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7624
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7622 uu____7623
                       in
                    uu____7617 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____7709 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____7709
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___384_7716 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___384_7716.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___384_7716.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___384_7716.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___384_7716.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___384_7716.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___384_7716.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___384_7716.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___384_7716.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___384_7716.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___384_7716.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___384_7716.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___384_7716.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___384_7716.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___384_7716.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___384_7716.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___384_7716.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___384_7716.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___384_7716.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___384_7716.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___384_7716.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___384_7716.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___384_7716.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___384_7716.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___384_7716.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___384_7716.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___384_7716.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___384_7716.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___384_7716.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___384_7716.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___384_7716.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___384_7716.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___384_7716.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___384_7716.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___384_7716.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___384_7716.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___384_7716.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___384_7716.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___384_7716.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___384_7716.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___384_7716.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___384_7716.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___384_7716.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____7766 = FStar_Syntax_Util.abs_formals e  in
                match uu____7766 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____7848::uu____7849 ->
                         let uu____7870 =
                           let uu____7871 =
                             let uu____7874 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____7874
                              in
                           uu____7871.FStar_Syntax_Syntax.n  in
                         (match uu____7870 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____7932 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____7932 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____7989 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____7989
                                   then
                                     let uu____8035 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8035 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8156  ->
                                                   fun uu____8157  ->
                                                     match (uu____8156,
                                                             uu____8157)
                                                     with
                                                     | ((x,uu____8183),
                                                        (b,uu____8185)) ->
                                                         let uu____8206 =
                                                           let uu____8213 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8213)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8206)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8221 =
                                            let uu____8250 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8250)  in
                                          (uu____8221, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8349 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8349 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8522) ->
                              let uu____8527 =
                                let uu____8556 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8556  in
                              (uu____8527, true)
                          | uu____8649 when Prims.op_Negation norm1 ->
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
                          | uu____8652 ->
                              let uu____8653 =
                                let uu____8655 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____8657 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____8655 uu____8657
                                 in
                              failwith uu____8653)
                     | uu____8693 ->
                         let rec aux' t_norm2 =
                           let uu____8733 =
                             let uu____8734 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____8734.FStar_Syntax_Syntax.n  in
                           match uu____8733 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____8792 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____8792 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____8835 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____8835 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____8962) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____8967 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___386_9039  ->
                  match () with
                  | () ->
                      let uu____9046 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9046
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9062 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9125  ->
                                   fun lb  ->
                                     match uu____9125 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9180 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9180
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9186 =
                                             let uu____9195 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9195
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9186 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9062 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9325 =
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
                               | uu____9338 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9348 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9348 vars)
                                   else
                                     (let uu____9351 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9351)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9412;
                                    FStar_Syntax_Syntax.lbeff = uu____9413;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9415;
                                    FStar_Syntax_Syntax.lbpos = uu____9416;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9440 =
                                     let uu____9449 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9449 with
                                     | (tcenv',uu____9467,e_t) ->
                                         let uu____9473 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9490 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____9473 with
                                          | (e1,t_norm1) ->
                                              ((let uu___387_9517 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___387_9517.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9440 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9531 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9531 with
                                         | ((binders,body,uu____9553,t_body),curry)
                                             ->
                                             ((let uu____9567 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9567
                                               then
                                                 let uu____9572 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9575 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9572 uu____9575
                                               else ());
                                              (let uu____9580 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9580 with
                                               | (vars,guards,env'1,binder_decls,uu____9607)
                                                   ->
                                                   let body1 =
                                                     let uu____9621 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9621
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
                                                     let uu____9645 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____9645 curry
                                                       fvb vars
                                                      in
                                                   let uu____9646 =
                                                     let is_logical =
                                                       let uu____9659 =
                                                         let uu____9660 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____9660.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____9659 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____9666 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____9670 =
                                                         let uu____9671 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____9671
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____9670
                                                         (fun lid  ->
                                                            let uu____9680 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____9680
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____9681 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____9681
                                                     then
                                                       let uu____9697 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____9698 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____9697,
                                                         uu____9698)
                                                     else
                                                       (let uu____9709 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____9709))
                                                      in
                                                   (match uu____9646 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____9733 =
                                                            let uu____9741 =
                                                              let uu____9742
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____9743
                                                                =
                                                                let uu____9754
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____9754)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____9742
                                                                uu____9743
                                                               in
                                                            let uu____9763 =
                                                              let uu____9764
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____9764
                                                               in
                                                            (uu____9741,
                                                              uu____9763,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____9733
                                                           in
                                                        let uu____9770 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____9770
                                                         with
                                                         | (pt_axioms,env3)
                                                             ->
                                                             ((FStar_List.append
                                                                 decls1
                                                                 (FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    [eqn]
                                                                    pt_axioms)))),
                                                               env3)))))))
                               | uu____9791 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9856 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____9856,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____9862 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9915  ->
                                         fun fvb  ->
                                           match uu____9915 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____9970 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9970
                                                  in
                                               let gtok =
                                                 let uu____9974 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9974
                                                  in
                                               let env4 =
                                                 let uu____9977 =
                                                   let uu____9980 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____9980
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9977
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____9862 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10107
                                     t_norm uu____10109 =
                                     match (uu____10107, uu____10109) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10141;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10142;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10144;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10145;_})
                                         ->
                                         let uu____10172 =
                                           let uu____10181 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10181 with
                                           | (tcenv',uu____10199,e_t) ->
                                               let uu____10205 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10222 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10205 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___388_10249 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___388_10249.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10172 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10268 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10268
                                                then
                                                  let uu____10273 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10275 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10277 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10273 uu____10275
                                                    uu____10277
                                                else ());
                                               (let uu____10282 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10282 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10322 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10322
                                                      then
                                                        let uu____10327 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10330 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10332 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10335 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10327
                                                          uu____10330
                                                          uu____10332
                                                          uu____10335
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10345 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10345 with
                                                      | (vars,guards,env'1,binder_decls,uu____10376)
                                                          ->
                                                          let decl_g =
                                                            let uu____10390 =
                                                              let uu____10402
                                                                =
                                                                let uu____10405
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10405
                                                                 in
                                                              (g,
                                                                uu____10402,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10390
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
                                                            let uu____10425 =
                                                              let uu____10433
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10433)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10425
                                                             in
                                                          let gsapp =
                                                            let uu____10440 =
                                                              let uu____10448
                                                                =
                                                                let uu____10451
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10451
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10448)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10440
                                                             in
                                                          let gmax =
                                                            let uu____10460 =
                                                              let uu____10468
                                                                =
                                                                let uu____10471
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____10471
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10468)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10460
                                                             in
                                                          let body1 =
                                                            let uu____10480 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____10480
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10485 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10485
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10503
                                                                   =
                                                                   let uu____10511
                                                                    =
                                                                    let uu____10512
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10513
                                                                    =
                                                                    let uu____10529
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
                                                                    uu____10529)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10512
                                                                    uu____10513
                                                                     in
                                                                   let uu____10543
                                                                    =
                                                                    let uu____10544
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10544
                                                                     in
                                                                   (uu____10511,
                                                                    uu____10543,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10503
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10551
                                                                   =
                                                                   let uu____10559
                                                                    =
                                                                    let uu____10560
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10561
                                                                    =
                                                                    let uu____10572
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10572)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10560
                                                                    uu____10561
                                                                     in
                                                                   (uu____10559,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10551
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10586
                                                                   =
                                                                   let uu____10594
                                                                    =
                                                                    let uu____10595
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10596
                                                                    =
                                                                    let uu____10607
                                                                    =
                                                                    let uu____10608
                                                                    =
                                                                    let uu____10613
                                                                    =
                                                                    let uu____10614
                                                                    =
                                                                    let uu____10622
                                                                    =
                                                                    let uu____10625
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10625
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10622)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10614
                                                                     in
                                                                    (gsapp,
                                                                    uu____10613)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10608
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10607)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10595
                                                                    uu____10596
                                                                     in
                                                                   (uu____10594,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10586
                                                                  in
                                                               let uu____10642
                                                                 =
                                                                 let uu____10651
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____10651
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____10680)
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
                                                                    let uu____10702
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10702
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____10704
                                                                    =
                                                                    let uu____10712
                                                                    =
                                                                    let uu____10713
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10714
                                                                    =
                                                                    let uu____10725
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10725)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10713
                                                                    uu____10714
                                                                     in
                                                                    (uu____10712,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10704
                                                                     in
                                                                    let uu____10738
                                                                    =
                                                                    let uu____10747
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____10747
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10762
                                                                    =
                                                                    let uu____10765
                                                                    =
                                                                    let uu____10766
                                                                    =
                                                                    let uu____10774
                                                                    =
                                                                    let uu____10775
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10776
                                                                    =
                                                                    let uu____10787
                                                                    =
                                                                    let uu____10788
                                                                    =
                                                                    let uu____10793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____10793,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____10788
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10787)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10775
                                                                    uu____10776
                                                                     in
                                                                    (uu____10774,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10766
                                                                     in
                                                                    [uu____10765]
                                                                     in
                                                                    (d3,
                                                                    uu____10762)
                                                                     in
                                                                    (match uu____10738
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
                                                               (match uu____10642
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
                                   let uu____10856 =
                                     let uu____10869 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____10932  ->
                                          fun uu____10933  ->
                                            match (uu____10932, uu____10933)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11058 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11058 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10869
                                      in
                                   (match uu____10856 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11131 =
                                          let isDeclFun uu___371_11146 =
                                            match uu___371_11146 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11148 -> true
                                            | uu____11161 -> false  in
                                          let uu____11163 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11163
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11131 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11203 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___372_11209  ->
                                        match uu___372_11209 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11212 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11220 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11220)))
                                in
                             if uu____11203
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___390_11242  ->
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
                   let uu____11280 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11280
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
        let uu____11350 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11350 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11356 = encode_sigelt' env se  in
      match uu____11356 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11368 =
                  let uu____11369 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11369  in
                [uu____11368]
            | uu____11372 ->
                let uu____11373 =
                  let uu____11376 =
                    let uu____11377 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11377  in
                  uu____11376 :: g  in
                let uu____11380 =
                  let uu____11383 =
                    let uu____11384 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11384  in
                  [uu____11383]  in
                FStar_List.append uu____11373 uu____11380
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
        let uu____11400 =
          let uu____11401 = FStar_Syntax_Subst.compress t  in
          uu____11401.FStar_Syntax_Syntax.n  in
        match uu____11400 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11406)) -> s = "opaque_to_smt"
        | uu____11411 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11420 =
          let uu____11421 = FStar_Syntax_Subst.compress t  in
          uu____11421.FStar_Syntax_Syntax.n  in
        match uu____11420 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11426)) -> s = "uninterpreted_by_smt"
        | uu____11431 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11437 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11443 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____11455 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____11456 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11457 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11470 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11472 =
            let uu____11474 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____11474  in
          if uu____11472
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11503 ->
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
               let uu____11535 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11535 with
               | (formals,uu____11555) ->
                   let arity = FStar_List.length formals  in
                   let uu____11579 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11579 with
                    | (aname,atok,env2) ->
                        let uu____11605 =
                          let uu____11610 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11610 env2
                           in
                        (match uu____11605 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11622 =
                                 let uu____11623 =
                                   let uu____11635 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____11655  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11635,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11623
                                  in
                               [uu____11622;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____11672 =
                               let aux uu____11733 uu____11734 =
                                 match (uu____11733, uu____11734) with
                                 | ((bv,uu____11793),(env3,acc_sorts,acc)) ->
                                     let uu____11840 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____11840 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____11672 with
                              | (uu____11924,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____11950 =
                                      let uu____11958 =
                                        let uu____11959 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____11960 =
                                          let uu____11971 =
                                            let uu____11972 =
                                              let uu____11977 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____11977)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____11972
                                             in
                                          ([[app]], xs_sorts, uu____11971)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____11959 uu____11960
                                         in
                                      (uu____11958,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11950
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
                                    let uu____11994 =
                                      let uu____12002 =
                                        let uu____12003 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12004 =
                                          let uu____12015 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12015)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12003 uu____12004
                                         in
                                      (uu____12002,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____11994
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12030 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12030 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12056,uu____12057)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12058 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12058 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12080,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12087 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___373_12093  ->
                      match uu___373_12093 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12096 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12102 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12105 -> false))
               in
            Prims.op_Negation uu____12087  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12115 =
               let uu____12122 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12122 env fv t quals  in
             match uu____12115 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12141 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12141 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12161 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12161 with
           | (uvs,f1) ->
               let env1 =
                 let uu___391_12173 = env  in
                 let uu____12174 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___391_12173.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___391_12173.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___391_12173.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12174;
                   FStar_SMTEncoding_Env.warn =
                     (uu___391_12173.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___391_12173.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___391_12173.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___391_12173.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___391_12173.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___391_12173.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___391_12173.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12176 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12176 with
                | (f3,decls) ->
                    let g =
                      let uu____12190 =
                        let uu____12191 =
                          let uu____12199 =
                            let uu____12200 =
                              let uu____12202 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12202
                               in
                            FStar_Pervasives_Native.Some uu____12200  in
                          let uu____12206 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12199, uu____12206)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12191  in
                      [uu____12190]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12211) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12225 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12247 =
                       let uu____12250 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12250.FStar_Syntax_Syntax.fv_name  in
                     uu____12247.FStar_Syntax_Syntax.v  in
                   let uu____12251 =
                     let uu____12253 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12253  in
                   if uu____12251
                   then
                     let val_decl =
                       let uu___392_12285 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___392_12285.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___392_12285.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___392_12285.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12286 = encode_sigelt' env1 val_decl  in
                     match uu____12286 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12225 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12322,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12324;
                          FStar_Syntax_Syntax.lbtyp = uu____12325;
                          FStar_Syntax_Syntax.lbeff = uu____12326;
                          FStar_Syntax_Syntax.lbdef = uu____12327;
                          FStar_Syntax_Syntax.lbattrs = uu____12328;
                          FStar_Syntax_Syntax.lbpos = uu____12329;_}::[]),uu____12330)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12349 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12349 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12392 =
                   let uu____12395 =
                     let uu____12396 =
                       let uu____12404 =
                         let uu____12405 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12406 =
                           let uu____12417 =
                             let uu____12418 =
                               let uu____12423 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12423)  in
                             FStar_SMTEncoding_Util.mkEq uu____12418  in
                           ([[b2t_x]], [xx], uu____12417)  in
                         FStar_SMTEncoding_Term.mkForall uu____12405
                           uu____12406
                          in
                       (uu____12404,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12396  in
                   [uu____12395]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12392
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____12455,uu____12456) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___374_12466  ->
                  match uu___374_12466 with
                  | FStar_Syntax_Syntax.Discriminator uu____12468 -> true
                  | uu____12470 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____12472,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____12484 =
                     let uu____12486 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____12486.FStar_Ident.idText  in
                   uu____12484 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___375_12493  ->
                     match uu___375_12493 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12496 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12499) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___376_12513  ->
                  match uu___376_12513 with
                  | FStar_Syntax_Syntax.Projector uu____12515 -> true
                  | uu____12521 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12525 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12525 with
           | FStar_Pervasives_Native.Some uu____12532 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___393_12534 = se  in
                 let uu____12535 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12535;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___393_12534.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___393_12534.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___393_12534.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12538) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12553) ->
          let uu____12562 = encode_sigelts env ses  in
          (match uu____12562 with
           | (g,env1) ->
               let uu____12579 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___377_12602  ->
                         match uu___377_12602 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12604;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12605;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12606;_}
                             -> false
                         | uu____12613 -> true))
                  in
               (match uu____12579 with
                | (g',inversions) ->
                    let uu____12629 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___378_12650  ->
                              match uu___378_12650 with
                              | FStar_SMTEncoding_Term.DeclFun uu____12652 ->
                                  true
                              | uu____12665 -> false))
                       in
                    (match uu____12629 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12682,tps,k,uu____12685,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___379_12704  ->
                    match uu___379_12704 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12708 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____12721 = c  in
              match uu____12721 with
              | (name,args,uu____12726,uu____12727,uu____12728) ->
                  let uu____12739 =
                    let uu____12740 =
                      let uu____12752 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____12779  ->
                                match uu____12779 with
                                | (uu____12788,sort,uu____12790) -> sort))
                         in
                      (name, uu____12752, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12740  in
                  [uu____12739]
            else
              (let uu____12801 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____12801 c)
             in
          let inversion_axioms tapp vars =
            let uu____12829 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____12837 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____12837 FStar_Option.isNone))
               in
            if uu____12829
            then []
            else
              (let uu____12872 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____12872 with
               | (xxsym,xx) ->
                   let uu____12885 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____12924  ->
                             fun l  ->
                               match uu____12924 with
                               | (out,decls) ->
                                   let uu____12944 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____12944 with
                                    | (uu____12955,data_t) ->
                                        let uu____12957 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____12957 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13001 =
                                                 let uu____13002 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13002.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13001 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13005,indices) ->
                                                   indices
                                               | uu____13031 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13061  ->
                                                         match uu____13061
                                                         with
                                                         | (x,uu____13069) ->
                                                             let uu____13074
                                                               =
                                                               let uu____13075
                                                                 =
                                                                 let uu____13083
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13083,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13075
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13074)
                                                    env)
                                                in
                                             let uu____13088 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13088 with
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
                                                      let uu____13118 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13136
                                                                 =
                                                                 let uu____13141
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13141,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13136)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13118
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13144 =
                                                      let uu____13145 =
                                                        let uu____13150 =
                                                          let uu____13151 =
                                                            let uu____13156 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13156,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13151
                                                           in
                                                        (out, uu____13150)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13145
                                                       in
                                                    (uu____13144,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____12885 with
                    | (data_ax,decls) ->
                        let uu____13169 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13169 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13186 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13186 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13193 =
                                 let uu____13201 =
                                   let uu____13202 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13203 =
                                     let uu____13214 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13227 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13214,
                                       uu____13227)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13202 uu____13203
                                    in
                                 let uu____13236 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13201,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13236)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13193
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13242 =
            let uu____13247 =
              let uu____13248 = FStar_Syntax_Subst.compress k  in
              uu____13248.FStar_Syntax_Syntax.n  in
            match uu____13247 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13283 -> (tps, k)  in
          (match uu____13242 with
           | (formals,res) ->
               let uu____13290 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13290 with
                | (formals1,res1) ->
                    let uu____13301 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13301 with
                     | (vars,guards,env',binder_decls,uu____13326) ->
                         let arity = FStar_List.length vars  in
                         let uu____13340 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13340 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13370 =
                                  let uu____13378 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13378)  in
                                FStar_SMTEncoding_Util.mkApp uu____13370  in
                              let uu____13384 =
                                let tname_decl =
                                  let uu____13394 =
                                    let uu____13395 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13423  ->
                                              match uu____13423 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13444 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13395,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13444, false)
                                     in
                                  constructor_or_logic_type_decl uu____13394
                                   in
                                let uu____13452 =
                                  match vars with
                                  | [] ->
                                      let uu____13465 =
                                        let uu____13466 =
                                          let uu____13469 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____13469
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____13466
                                         in
                                      ([], uu____13465)
                                  | uu____13481 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13491 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13491
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13507 =
                                          let uu____13515 =
                                            let uu____13516 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13517 =
                                              let uu____13533 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13533)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13516 uu____13517
                                             in
                                          (uu____13515,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13507
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13452 with
                                | (tok_decls,env2) ->
                                    let uu____13560 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13560
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13384 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13588 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13588 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13610 =
                                               let uu____13611 =
                                                 let uu____13619 =
                                                   let uu____13620 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13620
                                                    in
                                                 (uu____13619,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13611
                                                in
                                             [uu____13610]
                                           else []  in
                                         let uu____13628 =
                                           let uu____13631 =
                                             let uu____13634 =
                                               let uu____13635 =
                                                 let uu____13643 =
                                                   let uu____13644 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____13645 =
                                                     let uu____13656 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13656)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____13644 uu____13645
                                                    in
                                                 (uu____13643,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13635
                                                in
                                             [uu____13634]  in
                                           FStar_List.append karr uu____13631
                                            in
                                         FStar_List.append decls1 uu____13628
                                      in
                                   let aux =
                                     let uu____13671 =
                                       let uu____13674 =
                                         inversion_axioms tapp vars  in
                                       let uu____13677 =
                                         let uu____13680 =
                                           let uu____13681 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____13681 env2
                                             tapp vars
                                            in
                                         [uu____13680]  in
                                       FStar_List.append uu____13674
                                         uu____13677
                                        in
                                     FStar_List.append kindingAx uu____13671
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13686,uu____13687,uu____13688,uu____13689,uu____13690)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13698,t,uu____13700,n_tps,uu____13702) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____13712 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____13712 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____13760 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____13760 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____13788 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____13788 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13808 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____13808 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____13887 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____13887,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____13894 =
                                  let uu____13895 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____13895, true)
                                   in
                                let uu____13903 =
                                  let uu____13910 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____13910
                                   in
                                FStar_All.pipe_right uu____13894 uu____13903
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
                              let uu____13922 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____13922 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____13934::uu____13935 ->
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
                                         let uu____13994 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____13995 =
                                           let uu____14006 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14006)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____13994 uu____13995
                                     | uu____14027 -> tok_typing  in
                                   let uu____14038 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14038 with
                                    | (vars',guards',env'',decls_formals,uu____14063)
                                        ->
                                        let uu____14076 =
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
                                        (match uu____14076 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14106 ->
                                                   let uu____14115 =
                                                     let uu____14116 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14116
                                                      in
                                                   [uu____14115]
                                                in
                                             let encode_elim uu____14132 =
                                               let uu____14133 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14133 with
                                               | (head1,args) ->
                                                   let uu____14184 =
                                                     let uu____14185 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14185.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14184 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14197;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14198;_},uu____14199)
                                                        ->
                                                        let uu____14204 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14204
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14225
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14225
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
                                                                    uu____14279
                                                                    ->
                                                                    let uu____14280
                                                                    =
                                                                    let uu____14286
                                                                    =
                                                                    let uu____14288
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14288
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14286)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14280
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14308
                                                                    =
                                                                    let uu____14310
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14310
                                                                     in
                                                                    if
                                                                    uu____14308
                                                                    then
                                                                    let uu____14326
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14326]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14329
                                                                    =
                                                                    let uu____14343
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14400
                                                                     ->
                                                                    fun
                                                                    uu____14401
                                                                     ->
                                                                    match 
                                                                    (uu____14400,
                                                                    uu____14401)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14512
                                                                    =
                                                                    let uu____14520
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14520
                                                                     in
                                                                    (match uu____14512
                                                                    with
                                                                    | 
                                                                    (uu____14534,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14545
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14545
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14550
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14550
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
                                                                    uu____14343
                                                                     in
                                                                  (match uu____14329
                                                                   with
                                                                   | 
                                                                   (uu____14571,arg_vars,elim_eqns_or_guards,uu____14574)
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
                                                                    let uu____14601
                                                                    =
                                                                    let uu____14609
                                                                    =
                                                                    let uu____14610
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14611
                                                                    =
                                                                    let uu____14622
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14624
                                                                    =
                                                                    let uu____14625
                                                                    =
                                                                    let uu____14630
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14630)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14625
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14622,
                                                                    uu____14624)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14610
                                                                    uu____14611
                                                                     in
                                                                    (uu____14609,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14601
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14645
                                                                    =
                                                                    let uu____14651
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14651,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14645
                                                                     in
                                                                    let uu____14654
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14654
                                                                    then
                                                                    let x =
                                                                    let uu____14663
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14663,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14668
                                                                    =
                                                                    let uu____14676
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14678
                                                                    =
                                                                    let uu____14689
                                                                    =
                                                                    let uu____14694
                                                                    =
                                                                    let uu____14697
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14697]
                                                                     in
                                                                    [uu____14694]
                                                                     in
                                                                    let uu____14702
                                                                    =
                                                                    let uu____14703
                                                                    =
                                                                    let uu____14708
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14710
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14708,
                                                                    uu____14710)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14703
                                                                     in
                                                                    (uu____14689,
                                                                    [x],
                                                                    uu____14702)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14677
                                                                    uu____14678
                                                                     in
                                                                    let uu____14725
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14676,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14725)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14668
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14736
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
                                                                    (let uu____14774
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14775
                                                                    dapp1  in
                                                                    [uu____14774])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14736
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14792
                                                                    =
                                                                    let uu____14803
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14805
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14811)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14806
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14803,
                                                                    uu____14805)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14791
                                                                    uu____14792
                                                                     in
                                                                    (uu____14790,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14782)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____14829 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14829
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14850
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14850
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
                                                                    uu____14904
                                                                    ->
                                                                    let uu____14905
                                                                    =
                                                                    let uu____14911
                                                                    =
                                                                    let uu____14913
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14913
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14911)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14905
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14933
                                                                    =
                                                                    let uu____14935
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14935
                                                                     in
                                                                    if
                                                                    uu____14933
                                                                    then
                                                                    let uu____14951
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14951]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14954
                                                                    =
                                                                    let uu____14968
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15025
                                                                     ->
                                                                    fun
                                                                    uu____15026
                                                                     ->
                                                                    match 
                                                                    (uu____15025,
                                                                    uu____15026)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15137
                                                                    =
                                                                    let uu____15145
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15145
                                                                     in
                                                                    (match uu____15137
                                                                    with
                                                                    | 
                                                                    (uu____15159,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15170
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15170
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15175
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15175
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
                                                                    uu____14968
                                                                     in
                                                                  (match uu____14954
                                                                   with
                                                                   | 
                                                                   (uu____15196,arg_vars,elim_eqns_or_guards,uu____15199)
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
                                                                    let uu____15226
                                                                    =
                                                                    let uu____15234
                                                                    =
                                                                    let uu____15235
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15236
                                                                    =
                                                                    let uu____15247
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15249
                                                                    =
                                                                    let uu____15250
                                                                    =
                                                                    let uu____15255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15250
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15247,
                                                                    uu____15249)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15235
                                                                    uu____15236
                                                                     in
                                                                    (uu____15234,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15226
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15270
                                                                    =
                                                                    let uu____15276
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15276,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15270
                                                                     in
                                                                    let uu____15279
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15279
                                                                    then
                                                                    let x =
                                                                    let uu____15288
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15288,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15293
                                                                    =
                                                                    let uu____15301
                                                                    =
                                                                    let uu____15302
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15303
                                                                    =
                                                                    let uu____15314
                                                                    =
                                                                    let uu____15319
                                                                    =
                                                                    let uu____15322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15322]
                                                                     in
                                                                    [uu____15319]
                                                                     in
                                                                    let uu____15327
                                                                    =
                                                                    let uu____15328
                                                                    =
                                                                    let uu____15333
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15335
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15333,
                                                                    uu____15335)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15328
                                                                     in
                                                                    (uu____15314,
                                                                    [x],
                                                                    uu____15327)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15302
                                                                    uu____15303
                                                                     in
                                                                    let uu____15350
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15301,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15350)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15293
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15361
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
                                                                    (let uu____15399
                                                                    =
                                                                    let uu____15400
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15400
                                                                    dapp1  in
                                                                    [uu____15399])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15361
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15407
                                                                    =
                                                                    let uu____15415
                                                                    =
                                                                    let uu____15416
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15417
                                                                    =
                                                                    let uu____15428
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15430
                                                                    =
                                                                    let uu____15431
                                                                    =
                                                                    let uu____15436
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15436)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15431
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15428,
                                                                    uu____15430)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15416
                                                                    uu____15417
                                                                     in
                                                                    (uu____15415,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15407)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15453 ->
                                                        ((let uu____15455 =
                                                            let uu____15461 =
                                                              let uu____15463
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____15465
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____15463
                                                                uu____15465
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____15461)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15455);
                                                         ([], [])))
                                                in
                                             let uu____15473 = encode_elim ()
                                                in
                                             (match uu____15473 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15499 =
                                                      let uu____15502 =
                                                        let uu____15505 =
                                                          let uu____15508 =
                                                            let uu____15511 =
                                                              let uu____15512
                                                                =
                                                                let uu____15524
                                                                  =
                                                                  let uu____15525
                                                                    =
                                                                    let uu____15527
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15527
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15525
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15524)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15512
                                                               in
                                                            [uu____15511]  in
                                                          let uu____15534 =
                                                            let uu____15537 =
                                                              let uu____15540
                                                                =
                                                                let uu____15543
                                                                  =
                                                                  let uu____15546
                                                                    =
                                                                    let uu____15549
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15554
                                                                    =
                                                                    let uu____15557
                                                                    =
                                                                    let uu____15558
                                                                    =
                                                                    let uu____15566
                                                                    =
                                                                    let uu____15567
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15568
                                                                    =
                                                                    let uu____15579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15579)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15567
                                                                    uu____15568
                                                                     in
                                                                    (uu____15566,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15558
                                                                     in
                                                                    let uu____15592
                                                                    =
                                                                    let uu____15595
                                                                    =
                                                                    let uu____15596
                                                                    =
                                                                    let uu____15604
                                                                    =
                                                                    let uu____15605
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15606
                                                                    =
                                                                    let uu____15617
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15619
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15617,
                                                                    uu____15619)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15605
                                                                    uu____15606
                                                                     in
                                                                    (uu____15604,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15596
                                                                     in
                                                                    [uu____15595]
                                                                     in
                                                                    uu____15557
                                                                    ::
                                                                    uu____15592
                                                                     in
                                                                    uu____15549
                                                                    ::
                                                                    uu____15554
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15546
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15543
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15540
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15537
                                                             in
                                                          FStar_List.append
                                                            uu____15508
                                                            uu____15534
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15505
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15502
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15499
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
           (fun uu____15657  ->
              fun se  ->
                match uu____15657 with
                | (g,env1) ->
                    let uu____15677 = encode_sigelt env1 se  in
                    (match uu____15677 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15745 =
        match uu____15745 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15782 ->
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
                 ((let uu____15790 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15790
                   then
                     let uu____15795 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15797 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15799 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15795 uu____15797 uu____15799
                   else ());
                  (let uu____15804 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15804 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15822 =
                         let uu____15830 =
                           let uu____15832 =
                             let uu____15834 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15834
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15832  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15830
                          in
                       (match uu____15822 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____15854 = FStar_Options.log_queries ()
                                 in
                              if uu____15854
                              then
                                let uu____15857 =
                                  let uu____15859 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15861 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15863 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15859 uu____15861 uu____15863
                                   in
                                FStar_Pervasives_Native.Some uu____15857
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____15887,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____15907 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____15907 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15934 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15934 with | (uu____15961,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____15977 'Auu____15978 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____15977 *
      'Auu____15978) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16051  ->
              match uu____16051 with
              | (l,uu____16064,uu____16065) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16116  ->
              match uu____16116 with
              | (l,uu____16131,uu____16132) ->
                  let uu____16143 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16146 =
                    let uu____16149 =
                      let uu____16150 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16150  in
                    [uu____16149]  in
                  uu____16143 :: uu____16146))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16179 =
      let uu____16182 =
        let uu____16183 = FStar_Util.psmap_empty ()  in
        let uu____16198 = FStar_Util.psmap_empty ()  in
        let uu____16201 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16205 =
          let uu____16207 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16207 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16183;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16198;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16201;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16205;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16182]  in
    FStar_ST.op_Colon_Equals last_env uu____16179
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16249 = FStar_ST.op_Bang last_env  in
      match uu____16249 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16277 ->
          let uu___394_16280 = e  in
          let uu____16281 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___394_16280.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___394_16280.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___394_16280.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___394_16280.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___394_16280.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___394_16280.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___394_16280.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___394_16280.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16281;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___394_16280.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16289 = FStar_ST.op_Bang last_env  in
    match uu____16289 with
    | [] -> failwith "Empty env stack"
    | uu____16316::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16348  ->
    let uu____16349 = FStar_ST.op_Bang last_env  in
    match uu____16349 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16409  ->
    let uu____16410 = FStar_ST.op_Bang last_env  in
    match uu____16410 with
    | [] -> failwith "Popping an empty stack"
    | uu____16437::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16474  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16527  ->
         let uu____16528 = snapshot_env ()  in
         match uu____16528 with
         | (env_depth,()) ->
             let uu____16550 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16550 with
              | (varops_depth,()) ->
                  let uu____16572 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16572 with
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
        (fun uu____16630  ->
           let uu____16631 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16631 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16726 = snapshot msg  in () 
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
        | (uu____16772::uu____16773,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___395_16781 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___395_16781.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___395_16781.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___395_16781.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16782 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16802 =
        let uu____16805 =
          let uu____16806 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16806  in
        let uu____16807 = open_fact_db_tags env  in uu____16805 ::
          uu____16807
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16802
  
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
      let uu____16834 = encode_sigelt env se  in
      match uu____16834 with
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
        let uu____16879 = FStar_Options.log_queries ()  in
        if uu____16879
        then
          let uu____16884 =
            let uu____16885 =
              let uu____16887 =
                let uu____16889 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16889 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16887  in
            FStar_SMTEncoding_Term.Caption uu____16885  in
          uu____16884 :: decls
        else decls  in
      (let uu____16908 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____16908
       then
         let uu____16911 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16911
       else ());
      (let env =
         let uu____16917 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____16917 tcenv  in
       let uu____16918 = encode_top_level_facts env se  in
       match uu____16918 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____16932 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____16932)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____16946 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____16946
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____16961 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____16961
          then
            let uu____16964 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____16964
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17010  ->
                    fun se  ->
                      match uu____17010 with
                      | (g,env2) ->
                          let uu____17030 = encode_top_level_facts env2 se
                             in
                          (match uu____17030 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17053 =
            encode_signature
              (let uu___396_17062 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___396_17062.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___396_17062.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___396_17062.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___396_17062.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___396_17062.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___396_17062.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___396_17062.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___396_17062.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___396_17062.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___396_17062.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17053 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17082 = FStar_Options.log_queries ()  in
                if uu____17082
                then
                  let msg = Prims.strcat "Externals for " name  in
                  [FStar_SMTEncoding_Term.Module
                     (name,
                       (FStar_List.append
                          ((FStar_SMTEncoding_Term.Caption msg) :: decls1)
                          [FStar_SMTEncoding_Term.Caption
                             (Prims.strcat "End " msg)]))]
                else decls1  in
              (set_env
                 (let uu___397_17099 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___397_17099.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___397_17099.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___397_17099.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___397_17099.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___397_17099.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___397_17099.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___397_17099.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___397_17099.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___397_17099.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___397_17099.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17102 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17102
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
        (let uu____17167 =
           let uu____17169 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17169.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17167);
        (let env =
           let uu____17171 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17171 tcenv  in
         let uu____17172 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17211 = aux rest  in
                 (match uu____17211 with
                  | (out,rest1) ->
                      let t =
                        let uu____17239 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17239 with
                        | FStar_Pervasives_Native.Some uu____17242 ->
                            let uu____17243 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17243
                              x.FStar_Syntax_Syntax.sort
                        | uu____17244 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17248 =
                        let uu____17251 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___398_17254 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___398_17254.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___398_17254.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17251 :: out  in
                      (uu____17248, rest1))
             | uu____17259 -> ([], bindings)  in
           let uu____17266 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17266 with
           | (closing,bindings) ->
               let uu____17293 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17293, bindings)
            in
         match uu____17172 with
         | (q1,bindings) ->
             let uu____17324 = encode_env_bindings env bindings  in
             (match uu____17324 with
              | (env_decls,env1) ->
                  ((let uu____17346 =
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
                    if uu____17346
                    then
                      let uu____17353 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17353
                    else ());
                   (let uu____17358 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17358 with
                    | (phi,qdecls) ->
                        let uu____17379 =
                          let uu____17384 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17384 phi
                           in
                        (match uu____17379 with
                         | (labels,phi1) ->
                             let uu____17401 = encode_labels labels  in
                             (match uu____17401 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17438 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17438
                                    then
                                      let uu____17443 =
                                        let uu____17444 =
                                          let uu____17446 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17446
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17444
                                         in
                                      [uu____17443]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17455 =
                                      let uu____17463 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17464 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17463,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17464)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17455
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
  