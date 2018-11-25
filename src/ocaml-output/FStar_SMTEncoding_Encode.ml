open Prims
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (Prims.string * FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list)
    ;
  is: FStar_Ident.lident -> Prims.bool }
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (Prims.string * FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list))
  = fun projectee  -> match projectee with | { mk = mk1; is;_} -> mk1 
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  -> match projectee with | { mk = mk1; is;_} -> is 
let (prims : prims_t) =
  let uu____151 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____151 with
  | (asym,a) ->
      let uu____162 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____162 with
       | (xsym,x) ->
           let uu____173 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____173 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____251 =
                      let uu____263 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____263, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____251  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____294 =
                      let uu____302 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____302)  in
                    FStar_SMTEncoding_Util.mkApp uu____294  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____318 =
                    let uu____321 =
                      let uu____324 =
                        let uu____327 =
                          let uu____328 =
                            let uu____336 =
                              let uu____337 =
                                let uu____348 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____348)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____337
                               in
                            (uu____336, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____328  in
                        let uu____360 =
                          let uu____363 =
                            let uu____364 =
                              let uu____372 =
                                let uu____373 =
                                  let uu____384 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____384)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____373
                                 in
                              (uu____372,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____364  in
                          [uu____363]  in
                        uu____327 :: uu____360  in
                      xtok_decl :: uu____324  in
                    xname_decl :: uu____321  in
                  (x1, xtok1, (FStar_List.length vars), uu____318)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let mk_unary_boolean_connective interp rng vname =
                  let macro_name =
                    Prims.strcat FStar_Ident.reserved_prefix vname  in
                  let i =
                    let uu____531 =
                      let uu____532 = FStar_SMTEncoding_Term.unboxBool x  in
                      interp uu____532  in
                    FStar_SMTEncoding_Term.boxBool uu____531  in
                  let uu____533 =
                    let uu____546 = quant qx i  in uu____546 rng vname  in
                  match uu____533 with
                  | (uu____580,tok,arity,decls) ->
                      let macro =
                        FStar_SMTEncoding_Term.mkDefineFun
                          (macro_name, qx, FStar_SMTEncoding_Term.Term_sort,
                            i,
                            (FStar_Pervasives_Native.Some
                               (Prims.strcat vname " macro")))
                         in
                      (macro_name, tok, arity,
                        (FStar_List.append decls [macro]))
                   in
                let mk_binary_boolean_connective interp rng vname =
                  let macro_name =
                    Prims.strcat FStar_Ident.reserved_prefix vname  in
                  let i =
                    let uu____665 =
                      let uu____666 =
                        let uu____671 = FStar_SMTEncoding_Term.unboxBool x
                           in
                        let uu____672 = FStar_SMTEncoding_Term.unboxBool y
                           in
                        (uu____671, uu____672)  in
                      interp uu____666  in
                    FStar_SMTEncoding_Term.boxBool uu____665  in
                  let uu____673 =
                    let uu____686 = quant xy i  in uu____686 rng vname  in
                  match uu____673 with
                  | (uu____720,tok,arity,decls) ->
                      let macro =
                        FStar_SMTEncoding_Term.mkDefineFun
                          (macro_name, xy, FStar_SMTEncoding_Term.Term_sort,
                            i,
                            (FStar_Pervasives_Native.Some
                               (Prims.strcat vname " macro")))
                         in
                      (macro_name, tok, arity,
                        (FStar_List.append decls [macro]))
                   in
                let mk_op_not =
                  mk_unary_boolean_connective FStar_SMTEncoding_Util.mkNot
                   in
                let mk_op_and =
                  mk_binary_boolean_connective FStar_SMTEncoding_Util.mkAnd
                   in
                let mk_op_or =
                  mk_binary_boolean_connective FStar_SMTEncoding_Util.mkOr
                   in
                let prims1 =
                  let uu____839 =
                    let uu____863 =
                      let uu____885 =
                        let uu____886 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____886
                         in
                      quant axy uu____885  in
                    (FStar_Parser_Const.op_Eq, uu____863)  in
                  let uu____906 =
                    let uu____932 =
                      let uu____956 =
                        let uu____978 =
                          let uu____979 =
                            let uu____980 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____980  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____979
                           in
                        quant axy uu____978  in
                      (FStar_Parser_Const.op_notEq, uu____956)  in
                    let uu____1000 =
                      let uu____1026 =
                        let uu____1050 =
                          let uu____1072 =
                            let uu____1073 =
                              let uu____1074 =
                                let uu____1079 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____1080 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____1079, uu____1080)  in
                              FStar_SMTEncoding_Util.mkLT uu____1074  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____1073
                             in
                          quant xy uu____1072  in
                        (FStar_Parser_Const.op_LT, uu____1050)  in
                      let uu____1100 =
                        let uu____1126 =
                          let uu____1150 =
                            let uu____1172 =
                              let uu____1173 =
                                let uu____1174 =
                                  let uu____1179 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____1180 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____1179, uu____1180)  in
                                FStar_SMTEncoding_Util.mkLTE uu____1174  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1173
                               in
                            quant xy uu____1172  in
                          (FStar_Parser_Const.op_LTE, uu____1150)  in
                        let uu____1200 =
                          let uu____1226 =
                            let uu____1250 =
                              let uu____1272 =
                                let uu____1273 =
                                  let uu____1274 =
                                    let uu____1279 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____1280 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____1279, uu____1280)  in
                                  FStar_SMTEncoding_Util.mkGT uu____1274  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1273
                                 in
                              quant xy uu____1272  in
                            (FStar_Parser_Const.op_GT, uu____1250)  in
                          let uu____1300 =
                            let uu____1326 =
                              let uu____1350 =
                                let uu____1372 =
                                  let uu____1373 =
                                    let uu____1374 =
                                      let uu____1379 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1380 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1379, uu____1380)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1374
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1373
                                   in
                                quant xy uu____1372  in
                              (FStar_Parser_Const.op_GTE, uu____1350)  in
                            let uu____1400 =
                              let uu____1426 =
                                let uu____1450 =
                                  let uu____1472 =
                                    let uu____1473 =
                                      let uu____1474 =
                                        let uu____1479 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1480 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1479, uu____1480)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1474
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1473
                                     in
                                  quant xy uu____1472  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1450)
                                 in
                              let uu____1500 =
                                let uu____1526 =
                                  let uu____1550 =
                                    let uu____1572 =
                                      let uu____1573 =
                                        let uu____1574 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1574
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1573
                                       in
                                    quant qx uu____1572  in
                                  (FStar_Parser_Const.op_Minus, uu____1550)
                                   in
                                let uu____1594 =
                                  let uu____1620 =
                                    let uu____1644 =
                                      let uu____1666 =
                                        let uu____1667 =
                                          let uu____1668 =
                                            let uu____1673 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1674 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1673, uu____1674)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1668
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1667
                                         in
                                      quant xy uu____1666  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1644)
                                     in
                                  let uu____1694 =
                                    let uu____1720 =
                                      let uu____1744 =
                                        let uu____1766 =
                                          let uu____1767 =
                                            let uu____1768 =
                                              let uu____1773 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1774 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1773, uu____1774)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1768
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1767
                                           in
                                        quant xy uu____1766  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1744)
                                       in
                                    let uu____1794 =
                                      let uu____1820 =
                                        let uu____1844 =
                                          let uu____1866 =
                                            let uu____1867 =
                                              let uu____1868 =
                                                let uu____1873 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1874 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1873, uu____1874)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1868
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1867
                                             in
                                          quant xy uu____1866  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1844)
                                         in
                                      let uu____1894 =
                                        let uu____1920 =
                                          let uu____1944 =
                                            let uu____1966 =
                                              let uu____1967 =
                                                let uu____1968 =
                                                  let uu____1973 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1974 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1973, uu____1974)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1968
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1967
                                               in
                                            quant xy uu____1966  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1944)
                                           in
                                        [uu____1920;
                                        (FStar_Parser_Const.op_And,
                                          mk_op_and);
                                        (FStar_Parser_Const.op_Or, mk_op_or);
                                        (FStar_Parser_Const.op_Negation,
                                          mk_op_not)]
                                         in
                                      uu____1820 :: uu____1894  in
                                    uu____1720 :: uu____1794  in
                                  uu____1620 :: uu____1694  in
                                uu____1526 :: uu____1594  in
                              uu____1426 :: uu____1500  in
                            uu____1326 :: uu____1400  in
                          uu____1226 :: uu____1300  in
                        uu____1126 :: uu____1200  in
                      uu____1026 :: uu____1100  in
                    uu____932 :: uu____1000  in
                  uu____839 :: uu____906  in
                let mk1 l v1 =
                  let uu____2444 =
                    let uu____2459 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2561  ->
                              match uu____2561 with
                              | (l',uu____2585) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2459
                      (FStar_Option.map
                         (fun uu____2702  ->
                            match uu____2702 with
                            | (uu____2736,b) ->
                                let uu____2776 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2776 v1))
                     in
                  FStar_All.pipe_right uu____2444 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2874  ->
                          match uu____2874 with
                          | (l',uu____2898) -> FStar_Ident.lid_equals l l'))
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
          let uu____2972 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2972 with
          | (xxsym,xx) ->
              let uu____2983 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2983 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2999 =
                     let uu____3007 =
                       let uu____3008 =
                         let uu____3019 =
                           let uu____3020 =
                             let uu____3025 =
                               let uu____3026 =
                                 let uu____3031 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3031)  in
                               FStar_SMTEncoding_Util.mkEq uu____3026  in
                             (xx_has_type, uu____3025)  in
                           FStar_SMTEncoding_Util.mkImp uu____3020  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____3019)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____3008  in
                     let uu____3056 =
                       let uu____3058 =
                         let uu____3060 =
                           let uu____3062 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____3062  in
                         Prims.strcat module_name uu____3060  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3058
                        in
                     (uu____3007, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3056)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2999)
  
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
    let uu____3154 = f env.FStar_SMTEncoding_Env.tcenv s t  in
    (uu____3154, env)  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3174 =
      let uu____3175 =
        let uu____3183 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3183, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3175  in
    let uu____3188 =
      let uu____3191 =
        let uu____3192 =
          let uu____3200 =
            let uu____3201 =
              let uu____3212 =
                let uu____3213 =
                  let uu____3218 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3218)  in
                FStar_SMTEncoding_Util.mkImp uu____3213  in
              ([[typing_pred]], [xx], uu____3212)  in
            let uu____3237 =
              let uu____3252 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3252  in
            uu____3237 uu____3201  in
          (uu____3200, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3192  in
      [uu____3191]  in
    uu____3174 :: uu____3188  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3285 =
      let uu____3286 =
        let uu____3294 =
          let uu____3295 = FStar_TypeChecker_Env.get_range env  in
          let uu____3296 =
            let uu____3307 =
              let uu____3312 =
                let uu____3315 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3315]  in
              [uu____3312]  in
            let uu____3320 =
              let uu____3321 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3321 tt  in
            (uu____3307, [bb], uu____3320)  in
          FStar_SMTEncoding_Term.mkForall uu____3295 uu____3296  in
        (uu____3294, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3286  in
    let uu____3340 =
      let uu____3343 =
        let uu____3344 =
          let uu____3352 =
            let uu____3353 =
              let uu____3364 =
                let uu____3365 =
                  let uu____3370 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3370)  in
                FStar_SMTEncoding_Util.mkImp uu____3365  in
              ([[typing_pred]], [xx], uu____3364)  in
            let uu____3391 =
              let uu____3406 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3406  in
            uu____3391 uu____3353  in
          (uu____3352, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3344  in
      [uu____3343]  in
    uu____3285 :: uu____3340  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3430 =
        let uu____3436 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____3436, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____3430  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3460 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3460  in
    let uu____3465 =
      let uu____3466 =
        let uu____3474 =
          let uu____3475 = FStar_TypeChecker_Env.get_range env  in
          let uu____3476 =
            let uu____3487 =
              let uu____3492 =
                let uu____3495 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3495]  in
              [uu____3492]  in
            let uu____3500 =
              let uu____3501 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3501 tt  in
            (uu____3487, [bb], uu____3500)  in
          FStar_SMTEncoding_Term.mkForall uu____3475 uu____3476  in
        (uu____3474, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3466  in
    let uu____3520 =
      let uu____3523 =
        let uu____3524 =
          let uu____3532 =
            let uu____3533 =
              let uu____3544 =
                let uu____3545 =
                  let uu____3550 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3550)  in
                FStar_SMTEncoding_Util.mkImp uu____3545  in
              ([[typing_pred]], [xx], uu____3544)  in
            let uu____3571 =
              let uu____3586 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3586  in
            uu____3571 uu____3533  in
          (uu____3532, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3524  in
      let uu____3591 =
        let uu____3594 =
          let uu____3595 =
            let uu____3603 =
              let uu____3604 =
                let uu____3615 =
                  let uu____3616 =
                    let uu____3621 =
                      let uu____3622 =
                        let uu____3625 =
                          let uu____3628 =
                            let uu____3631 =
                              let uu____3632 =
                                let uu____3637 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3638 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3637, uu____3638)  in
                              FStar_SMTEncoding_Util.mkGT uu____3632  in
                            let uu____3640 =
                              let uu____3643 =
                                let uu____3644 =
                                  let uu____3649 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3650 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3649, uu____3650)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3644  in
                              let uu____3652 =
                                let uu____3655 =
                                  let uu____3656 =
                                    let uu____3661 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3662 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3661, uu____3662)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3656  in
                                [uu____3655]  in
                              uu____3643 :: uu____3652  in
                            uu____3631 :: uu____3640  in
                          typing_pred_y :: uu____3628  in
                        typing_pred :: uu____3625  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3622  in
                    (uu____3621, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3616  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3615)
                 in
              let uu____3686 =
                let uu____3701 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3701  in
              uu____3686 uu____3604  in
            (uu____3603,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3595  in
        [uu____3594]  in
      uu____3523 :: uu____3591  in
    uu____3465 :: uu____3520  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3734 =
      let uu____3735 =
        let uu____3743 =
          let uu____3744 = FStar_TypeChecker_Env.get_range env  in
          let uu____3745 =
            let uu____3756 =
              let uu____3761 =
                let uu____3764 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3764]  in
              [uu____3761]  in
            let uu____3769 =
              let uu____3770 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3770 tt  in
            (uu____3756, [bb], uu____3769)  in
          FStar_SMTEncoding_Term.mkForall uu____3744 uu____3745  in
        (uu____3743, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3735  in
    let uu____3789 =
      let uu____3792 =
        let uu____3793 =
          let uu____3801 =
            let uu____3802 =
              let uu____3813 =
                let uu____3814 =
                  let uu____3819 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3819)  in
                FStar_SMTEncoding_Util.mkImp uu____3814  in
              ([[typing_pred]], [xx], uu____3813)  in
            let uu____3840 =
              let uu____3855 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3855  in
            uu____3840 uu____3802  in
          (uu____3801, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3793  in
      [uu____3792]  in
    uu____3734 :: uu____3789  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3883 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3883]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3911 =
      let uu____3912 =
        let uu____3920 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3920, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3912  in
    [uu____3911]  in
  let mk_macro_name s = Prims.strcat FStar_Ident.reserved_prefix s  in
  let mkValid t = FStar_SMTEncoding_Util.mkApp ("Valid", [t])  in
  let mkBoxLogical t = FStar_SMTEncoding_Util.mkApp ("BoxLogical", [t])  in
  let squash env t =
    let sq =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.squash_lid  in
    let b2t1 =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.b2t_lid  in
    let uu____3967 =
      let uu____3975 =
        let uu____3978 =
          let uu____3979 =
            let uu____3987 =
              let uu____3990 = FStar_SMTEncoding_Term.boxBool t  in
              [uu____3990]  in
            ((b2t1.FStar_SMTEncoding_Env.smt_id), uu____3987)  in
          FStar_SMTEncoding_Util.mkApp uu____3979  in
        [uu____3978]  in
      ((sq.FStar_SMTEncoding_Env.smt_id), uu____3975)  in
    FStar_SMTEncoding_Util.mkApp uu____3967  in
  let bind_macro env lid macro_name =
    let fvb = FStar_SMTEncoding_Env.lookup_lid env lid  in
    FStar_SMTEncoding_Env.push_free_var env lid
      fvb.FStar_SMTEncoding_Env.smt_arity macro_name
      fvb.FStar_SMTEncoding_Env.smt_token
     in
  let mk_unary_prop_connective conn interp env vname uu____4049 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let conn_a = FStar_SMTEncoding_Util.mkApp (vname, [a])  in
    let valid_conn_a = mkValid conn_a  in
    let valid_a = mkValid a  in
    let macro_name = mk_macro_name vname  in
    let macro =
      let uu____4075 =
        let uu____4094 =
          let uu____4095 = interp valid_a  in mkBoxLogical uu____4095  in
        (macro_name, [aa], FStar_SMTEncoding_Term.Term_sort, uu____4094,
          (FStar_Pervasives_Native.Some "macro for embedded unary connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4075  in
    let uu____4116 =
      let uu____4117 =
        let uu____4118 =
          let uu____4126 =
            let uu____4127 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4128 =
              let uu____4139 =
                let uu____4140 =
                  let uu____4145 = interp valid_a  in
                  (uu____4145, valid_conn_a)  in
                FStar_SMTEncoding_Util.mkIff uu____4140  in
              ([[conn_a]], [aa], uu____4139)  in
            FStar_SMTEncoding_Term.mkForall uu____4127 uu____4128  in
          (uu____4126,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4118  in
      [uu____4117; macro]  in
    let uu____4168 = bind_macro env conn macro_name  in
    (uu____4116, uu____4168)  in
  let mk_binary_prop_connective conn interp env vname uu____4206 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let conn_a_b = FStar_SMTEncoding_Util.mkApp (vname, [a; b])  in
    let valid_conn_a_b = mkValid conn_a_b  in
    let valid_a = mkValid a  in
    let valid_b = mkValid b  in
    let macro_name = mk_macro_name vname  in
    let macro =
      let uu____4246 =
        let uu____4265 =
          let uu____4266 = interp (valid_a, valid_b)  in
          mkBoxLogical uu____4266  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4265,
          (FStar_Pervasives_Native.Some "macro for embedded connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4246  in
    let uu____4292 =
      let uu____4293 =
        let uu____4294 =
          let uu____4302 =
            let uu____4303 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4304 =
              let uu____4315 =
                let uu____4316 =
                  let uu____4321 = interp (valid_a, valid_b)  in
                  (uu____4321, valid_conn_a_b)  in
                FStar_SMTEncoding_Util.mkIff uu____4316  in
              ([[conn_a_b]], [aa; bb], uu____4315)  in
            FStar_SMTEncoding_Term.mkForall uu____4303 uu____4304  in
          (uu____4302,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4294  in
      [uu____4293; macro]  in
    let uu____4349 = bind_macro env conn macro_name  in
    (uu____4292, uu____4349)  in
  let mk_and_interp =
    mk_binary_prop_connective FStar_Parser_Const.and_lid
      FStar_SMTEncoding_Util.mkAnd
     in
  let mk_or_interp =
    mk_binary_prop_connective FStar_Parser_Const.or_lid
      FStar_SMTEncoding_Util.mkOr
     in
  let mk_imp_interp =
    mk_binary_prop_connective FStar_Parser_Const.imp_lid
      FStar_SMTEncoding_Util.mkImp
     in
  let mk_iff_interp =
    mk_binary_prop_connective FStar_Parser_Const.iff_lid
      FStar_SMTEncoding_Util.mkIff
     in
  let mk_not_interp =
    mk_unary_prop_connective FStar_Parser_Const.not_lid
      FStar_SMTEncoding_Util.mkNot
     in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____4494 =
      let uu____4495 =
        let uu____4503 =
          let uu____4504 = FStar_TypeChecker_Env.get_range env  in
          let uu____4505 =
            let uu____4516 =
              let uu____4517 =
                let uu____4522 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4522, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4517  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4516)  in
          FStar_SMTEncoding_Term.mkForall uu____4504 uu____4505  in
        (uu____4503, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4495  in
    [uu____4494]  in
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
    let uu____4618 =
      let uu____4619 =
        let uu____4627 =
          let uu____4628 = FStar_TypeChecker_Env.get_range env  in
          let uu____4629 =
            let uu____4640 =
              let uu____4641 =
                let uu____4646 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4646, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4641  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4640)  in
          FStar_SMTEncoding_Term.mkForall uu____4628 uu____4629  in
        (uu____4627, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4619  in
    [uu____4618]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4706 =
      let uu____4707 =
        let uu____4715 =
          let uu____4716 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4716 range_ty  in
        let uu____4717 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4715, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4717)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4707  in
    [uu____4706]  in
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
        let uu____4771 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4771 x1 t  in
      let uu____4773 = FStar_TypeChecker_Env.get_range env  in
      let uu____4774 =
        let uu____4785 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4785)  in
      FStar_SMTEncoding_Term.mkForall uu____4773 uu____4774  in
    let uu____4804 =
      let uu____4805 =
        let uu____4813 =
          let uu____4814 = FStar_TypeChecker_Env.get_range env  in
          let uu____4815 =
            let uu____4826 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4826)  in
          FStar_SMTEncoding_Term.mkForall uu____4814 uu____4815  in
        (uu____4813,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4805  in
    [uu____4804]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4889 =
      let uu____4890 =
        let uu____4898 =
          let uu____4899 = FStar_TypeChecker_Env.get_range env  in
          let uu____4900 =
            let uu____4916 =
              let uu____4917 =
                let uu____4922 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4923 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4922, uu____4923)  in
              FStar_SMTEncoding_Util.mkAnd uu____4917  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4916)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4899 uu____4900  in
        (uu____4898,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4890  in
    [uu____4889]  in
  let mk_squash_interp env sq uu____4972 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_sq_a =
      let uu____4989 =
        let uu____4997 =
          let uu____5000 = FStar_SMTEncoding_Util.mkApp (sq, [a])  in
          [uu____5000]  in
        ("Valid", uu____4997)  in
      FStar_SMTEncoding_Util.mkApp uu____4989  in
    let uu____5008 =
      let uu____5009 =
        let uu____5017 =
          let uu____5018 = FStar_TypeChecker_Env.get_range env  in
          let uu____5019 =
            let uu____5030 =
              FStar_SMTEncoding_Util.mkIff (valid_sq_a, valid_a)  in
            ([[valid_sq_a]], [aa], uu____5030)  in
          FStar_SMTEncoding_Term.mkForall uu____5018 uu____5019  in
        (uu____5017,
          (FStar_Pervasives_Native.Some "valid-squash interpretation"),
          "valid-squash-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____5009  in
    [uu____5008]  in
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
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.eq2_lid, (wrap mk_eq2_interp));
    (FStar_Parser_Const.eq3_lid, (wrap mk_eq3_interp));
    (FStar_Parser_Const.range_lid, (wrap mk_range_interp));
    (FStar_Parser_Const.inversion_lid, (wrap mk_inversion_axiom));
    (FStar_Parser_Const.with_type_lid, (wrap mk_with_type_axiom));
    (FStar_Parser_Const.squash_lid, (wrap mk_squash_interp))]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____5713 =
            FStar_Util.find_opt
              (fun uu____5759  ->
                 match uu____5759 with
                 | (l,uu____5779) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5713 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____5840,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5913 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5913 with
        | (form,decls) ->
            let uu____5922 =
              let uu____5925 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5925]  in
            FStar_List.append decls uu____5922
  
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
              let uu____5982 =
                ((let uu____5986 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5986) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5982
              then
                let arg_sorts =
                  let uu____6000 =
                    let uu____6001 = FStar_Syntax_Subst.compress t_norm  in
                    uu____6001.FStar_Syntax_Syntax.n  in
                  match uu____6000 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6007) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6045  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6052 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6054 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6054 with
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
                (let uu____6096 = prims.is lid  in
                 if uu____6096
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6107 = prims.mk lid vname  in
                   match uu____6107 with
                   | (vname1,tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname1 (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6147 =
                      let uu____6166 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6166 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6194 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6194
                            then
                              let uu____6199 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___438_6202 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___438_6202.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___438_6202.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___438_6202.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___438_6202.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___438_6202.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___438_6202.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___438_6202.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___438_6202.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___438_6202.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___438_6202.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___438_6202.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___438_6202.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___438_6202.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___438_6202.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___438_6202.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___438_6202.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___438_6202.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___438_6202.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___438_6202.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___438_6202.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___438_6202.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___438_6202.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___438_6202.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___438_6202.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___438_6202.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___438_6202.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___438_6202.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___438_6202.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___438_6202.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___438_6202.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___438_6202.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___438_6202.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___438_6202.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___438_6202.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___438_6202.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___438_6202.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___438_6202.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___438_6202.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___438_6202.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___438_6202.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___438_6202.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___438_6202.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6199
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6225 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6225)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6147 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6306 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6306 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6340 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___428_6401  ->
                                       match uu___428_6401 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6405 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6405 with
                                            | (uu____6429,(xxsym,uu____6431))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6455 =
                                                  let uu____6456 =
                                                    let uu____6464 =
                                                      let uu____6465 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6466 =
                                                        let uu____6477 =
                                                          let uu____6478 =
                                                            let uu____6483 =
                                                              let uu____6484
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6484
                                                               in
                                                            (vapp,
                                                              uu____6483)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6478
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6477)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6465 uu____6466
                                                       in
                                                    (uu____6464,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6456
                                                   in
                                                [uu____6455])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6499 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6499 with
                                            | (uu____6523,(xxsym,uu____6525))
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
                                                let uu____6557 =
                                                  let uu____6558 =
                                                    let uu____6566 =
                                                      let uu____6567 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6568 =
                                                        let uu____6579 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6579)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6567 uu____6568
                                                       in
                                                    (uu____6566,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6558
                                                   in
                                                [uu____6557])
                                       | uu____6592 -> []))
                                in
                             let uu____6593 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6593 with
                              | (vars,guards,env',decls1,uu____6620) ->
                                  let uu____6633 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6646 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6646, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6650 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6650 with
                                         | (g,ds) ->
                                             let uu____6663 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6663,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6633 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6680 =
                                           let uu____6688 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6688)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6680
                                          in
                                       let uu____6694 =
                                         let vname_decl =
                                           let uu____6702 =
                                             let uu____6714 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6734  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6714,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6702
                                            in
                                         let uu____6745 =
                                           let env2 =
                                             let uu___439_6751 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___439_6751.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____6752 =
                                             let uu____6754 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6754  in
                                           if uu____6752
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6745 with
                                         | (tok_typing,decls2) ->
                                             let uu____6771 =
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
                                                   let uu____6795 =
                                                     let uu____6796 =
                                                       let uu____6799 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6799
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6796
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6795)
                                               | uu____6809 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6824 =
                                                       let uu____6832 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6832]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6824
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6854 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6855 =
                                                       let uu____6866 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6866)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6854 uu____6855
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6876 =
                                                       let uu____6884 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6884,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6876
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
                                                       let uu____6923 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6924 =
                                                         let uu____6935 =
                                                           let uu____6936 =
                                                             let uu____6941 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6942 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6941,
                                                               uu____6942)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6936
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6935)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6923
                                                         uu____6924
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
                                             (match uu____6771 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6694 with
                                        | (decls2,env2) ->
                                            let uu____6993 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____7003 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____7003 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____7018 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____7018,
                                                    decls)
                                               in
                                            (match uu____6993 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____7035 =
                                                     let uu____7043 =
                                                       let uu____7044 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7045 =
                                                         let uu____7056 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____7056)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7044
                                                         uu____7045
                                                        in
                                                     (uu____7043,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7035
                                                    in
                                                 let freshness =
                                                   let uu____7072 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____7072
                                                   then
                                                     let uu____7080 =
                                                       let uu____7081 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7082 =
                                                         let uu____7095 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____7113 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____7095,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____7113)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____7081
                                                         uu____7082
                                                        in
                                                     let uu____7119 =
                                                       let uu____7122 =
                                                         let uu____7123 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____7123 env2
                                                           vapp vars
                                                          in
                                                       [uu____7122]  in
                                                     uu____7080 :: uu____7119
                                                   else []  in
                                                 let g =
                                                   let uu____7129 =
                                                     let uu____7132 =
                                                       let uu____7135 =
                                                         let uu____7138 =
                                                           let uu____7141 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____7141
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____7138
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____7135
                                                        in
                                                     FStar_List.append decls2
                                                       uu____7132
                                                      in
                                                   FStar_List.append decls11
                                                     uu____7129
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
          let uu____7183 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7183 with
          | FStar_Pervasives_Native.None  ->
              let uu____7194 = encode_free_var false env x t t_norm []  in
              (match uu____7194 with
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
            let uu____7265 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7265 with
            | (decls,env1) ->
                let uu____7284 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7284
                then
                  let uu____7293 =
                    let uu____7296 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7296  in
                  (uu____7293, env1)
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
             (fun uu____7356  ->
                fun lb  ->
                  match uu____7356 with
                  | (decls,env1) ->
                      let uu____7376 =
                        let uu____7383 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7383
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7376 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7416 = FStar_Syntax_Util.head_and_args t  in
    match uu____7416 with
    | (hd1,args) ->
        let uu____7460 =
          let uu____7461 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7461.FStar_Syntax_Syntax.n  in
        (match uu____7460 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7467,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7491 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7502 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___440_7510 = en  in
    let uu____7511 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___440_7510.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___440_7510.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___440_7510.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___440_7510.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___440_7510.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7511;
      FStar_SMTEncoding_Env.nolabels =
        (uu___440_7510.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___440_7510.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___440_7510.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___440_7510.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___440_7510.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7543  ->
      fun quals  ->
        match uu____7543 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7650 = FStar_Util.first_N nbinders formals  in
              match uu____7650 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7751  ->
                         fun uu____7752  ->
                           match (uu____7751, uu____7752) with
                           | ((formal,uu____7778),(binder,uu____7780)) ->
                               let uu____7801 =
                                 let uu____7808 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7808)  in
                               FStar_Syntax_Syntax.NT uu____7801) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7822 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7863  ->
                              match uu____7863 with
                              | (x,i) ->
                                  let uu____7882 =
                                    let uu___441_7883 = x  in
                                    let uu____7884 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___441_7883.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___441_7883.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7884
                                    }  in
                                  (uu____7882, i)))
                       in
                    FStar_All.pipe_right uu____7822
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7908 =
                      let uu____7913 = FStar_Syntax_Subst.compress body  in
                      let uu____7914 =
                        let uu____7915 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7915
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7913 uu____7914
                       in
                    uu____7908 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____8000 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____8000
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___442_8007 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___442_8007.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___442_8007.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___442_8007.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___442_8007.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___442_8007.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___442_8007.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___442_8007.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___442_8007.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___442_8007.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___442_8007.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___442_8007.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___442_8007.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___442_8007.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___442_8007.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___442_8007.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___442_8007.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___442_8007.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___442_8007.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___442_8007.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___442_8007.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___442_8007.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___442_8007.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___442_8007.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___442_8007.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___442_8007.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___442_8007.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___442_8007.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___442_8007.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___442_8007.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___442_8007.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___442_8007.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___442_8007.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___442_8007.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___442_8007.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___442_8007.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___442_8007.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___442_8007.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___442_8007.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___442_8007.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___442_8007.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___442_8007.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___442_8007.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____8057 = FStar_Syntax_Util.abs_formals e  in
                match uu____8057 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8139::uu____8140 ->
                         let uu____8161 =
                           let uu____8162 =
                             let uu____8165 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____8165
                              in
                           uu____8162.FStar_Syntax_Syntax.n  in
                         (match uu____8161 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8223 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8223 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____8280 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____8280
                                   then
                                     let uu____8326 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8326 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8447  ->
                                                   fun uu____8448  ->
                                                     match (uu____8447,
                                                             uu____8448)
                                                     with
                                                     | ((x,uu____8474),
                                                        (b,uu____8476)) ->
                                                         let uu____8497 =
                                                           let uu____8504 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8504)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8497)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8512 =
                                            let uu____8541 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8541)  in
                                          (uu____8512, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8640 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8640 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8813) ->
                              let uu____8818 =
                                let uu____8847 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8847  in
                              (uu____8818, true)
                          | uu____8940 when Prims.op_Negation norm1 ->
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
                          | uu____8943 ->
                              let uu____8944 =
                                let uu____8946 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____8948 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____8946 uu____8948
                                 in
                              failwith uu____8944)
                     | uu____8984 ->
                         let rec aux' t_norm2 =
                           let uu____9024 =
                             let uu____9025 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____9025.FStar_Syntax_Syntax.n  in
                           match uu____9024 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____9083 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____9083 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____9126 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____9126 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____9253) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____9258 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___444_9330  ->
                  match () with
                  | () ->
                      let uu____9337 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9337
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9353 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9416  ->
                                   fun lb  ->
                                     match uu____9416 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9471 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9471
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9477 =
                                             let uu____9486 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9486
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9477 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9353 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9616 =
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
                               | uu____9629 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9639 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9639 vars)
                                   else
                                     (let uu____9642 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9642)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9703;
                                    FStar_Syntax_Syntax.lbeff = uu____9704;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9706;
                                    FStar_Syntax_Syntax.lbpos = uu____9707;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9731 =
                                     let uu____9740 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9740 with
                                     | (tcenv',uu____9758,e_t) ->
                                         let uu____9764 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9781 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____9764 with
                                          | (e1,t_norm1) ->
                                              ((let uu___445_9808 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___445_9808.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9731 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9822 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9822 with
                                         | ((binders,body,uu____9844,t_body),curry)
                                             ->
                                             ((let uu____9858 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9858
                                               then
                                                 let uu____9863 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9866 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9863 uu____9866
                                               else ());
                                              (let uu____9871 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9871 with
                                               | (vars,guards,env'1,binder_decls,uu____9898)
                                                   ->
                                                   let body1 =
                                                     let uu____9912 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9912
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
                                                     let uu____9936 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____9936 curry
                                                       fvb vars
                                                      in
                                                   let uu____9937 =
                                                     let is_logical =
                                                       let uu____9950 =
                                                         let uu____9951 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____9951.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____9950 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____9957 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____9961 =
                                                         let uu____9962 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____9962
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____9961
                                                         (fun lid  ->
                                                            let uu____9971 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____9971
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____9972 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____9972
                                                     then
                                                       let uu____9988 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____9989 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____9988,
                                                         uu____9989)
                                                     else
                                                       (let uu____10000 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____10000))
                                                      in
                                                   (match uu____9937 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____10024 =
                                                            let uu____10032 =
                                                              let uu____10033
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____10034
                                                                =
                                                                let uu____10045
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____10045)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____10033
                                                                uu____10034
                                                               in
                                                            let uu____10054 =
                                                              let uu____10055
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____10055
                                                               in
                                                            (uu____10032,
                                                              uu____10054,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____10024
                                                           in
                                                        let uu____10061 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____10061
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
                               | uu____10082 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10147 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____10147,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10153 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10206  ->
                                         fun fvb  ->
                                           match uu____10206 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10261 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10261
                                                  in
                                               let gtok =
                                                 let uu____10265 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10265
                                                  in
                                               let env4 =
                                                 let uu____10268 =
                                                   let uu____10271 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10271
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10268
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10153 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10398
                                     t_norm uu____10400 =
                                     match (uu____10398, uu____10400) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10432;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10433;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10435;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10436;_})
                                         ->
                                         let uu____10463 =
                                           let uu____10472 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10472 with
                                           | (tcenv',uu____10490,e_t) ->
                                               let uu____10496 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10513 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10496 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___446_10540 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___446_10540.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10463 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10559 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10559
                                                then
                                                  let uu____10564 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10566 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10568 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10564 uu____10566
                                                    uu____10568
                                                else ());
                                               (let uu____10573 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10573 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10613 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10613
                                                      then
                                                        let uu____10618 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10621 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10623 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10626 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10618
                                                          uu____10621
                                                          uu____10623
                                                          uu____10626
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10636 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10636 with
                                                      | (vars,guards,env'1,binder_decls,uu____10667)
                                                          ->
                                                          let decl_g =
                                                            let uu____10681 =
                                                              let uu____10693
                                                                =
                                                                let uu____10696
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10696
                                                                 in
                                                              (g,
                                                                uu____10693,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10681
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
                                                            let uu____10716 =
                                                              let uu____10724
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10724)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10716
                                                             in
                                                          let gsapp =
                                                            let uu____10731 =
                                                              let uu____10739
                                                                =
                                                                let uu____10742
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10742
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10739)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10731
                                                             in
                                                          let gmax =
                                                            let uu____10751 =
                                                              let uu____10759
                                                                =
                                                                let uu____10762
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____10762
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10759)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10751
                                                             in
                                                          let body1 =
                                                            let uu____10771 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____10771
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10776 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10776
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10794
                                                                   =
                                                                   let uu____10802
                                                                    =
                                                                    let uu____10803
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10804
                                                                    =
                                                                    let uu____10820
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
                                                                    uu____10820)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10803
                                                                    uu____10804
                                                                     in
                                                                   let uu____10834
                                                                    =
                                                                    let uu____10835
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10835
                                                                     in
                                                                   (uu____10802,
                                                                    uu____10834,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10794
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10842
                                                                   =
                                                                   let uu____10850
                                                                    =
                                                                    let uu____10851
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10852
                                                                    =
                                                                    let uu____10863
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10863)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10851
                                                                    uu____10852
                                                                     in
                                                                   (uu____10850,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10842
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10877
                                                                   =
                                                                   let uu____10885
                                                                    =
                                                                    let uu____10886
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10887
                                                                    =
                                                                    let uu____10898
                                                                    =
                                                                    let uu____10899
                                                                    =
                                                                    let uu____10904
                                                                    =
                                                                    let uu____10905
                                                                    =
                                                                    let uu____10913
                                                                    =
                                                                    let uu____10916
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10916
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10913)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10905
                                                                     in
                                                                    (gsapp,
                                                                    uu____10904)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10899
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10898)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10886
                                                                    uu____10887
                                                                     in
                                                                   (uu____10885,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10877
                                                                  in
                                                               let uu____10933
                                                                 =
                                                                 let uu____10942
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____10942
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____10971)
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
                                                                    let uu____10993
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10993
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____10995
                                                                    =
                                                                    let uu____11003
                                                                    =
                                                                    let uu____11004
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11005
                                                                    =
                                                                    let uu____11016
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11016)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11004
                                                                    uu____11005
                                                                     in
                                                                    (uu____11003,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10995
                                                                     in
                                                                    let uu____11029
                                                                    =
                                                                    let uu____11038
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____11038
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11053
                                                                    =
                                                                    let uu____11056
                                                                    =
                                                                    let uu____11057
                                                                    =
                                                                    let uu____11065
                                                                    =
                                                                    let uu____11066
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11067
                                                                    =
                                                                    let uu____11078
                                                                    =
                                                                    let uu____11079
                                                                    =
                                                                    let uu____11084
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____11084,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11079
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11078)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11066
                                                                    uu____11067
                                                                     in
                                                                    (uu____11065,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11057
                                                                     in
                                                                    [uu____11056]
                                                                     in
                                                                    (d3,
                                                                    uu____11053)
                                                                     in
                                                                    (match uu____11029
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
                                                               (match uu____10933
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
                                   let uu____11147 =
                                     let uu____11160 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11223  ->
                                          fun uu____11224  ->
                                            match (uu____11223, uu____11224)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11349 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11349 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11160
                                      in
                                   (match uu____11147 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11422 =
                                          let isDeclFun uu___429_11437 =
                                            match uu___429_11437 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11439 -> true
                                            | uu____11452 -> false  in
                                          let uu____11454 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11454
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11422 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11494 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___430_11500  ->
                                        match uu___430_11500 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11503 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11511 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11511)))
                                in
                             if uu____11494
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___448_11533  ->
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
                   let uu____11571 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11571
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
        let uu____11641 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11641 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11647 = encode_sigelt' env se  in
      match uu____11647 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11659 =
                  let uu____11660 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11660  in
                [uu____11659]
            | uu____11663 ->
                let uu____11664 =
                  let uu____11667 =
                    let uu____11668 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11668  in
                  uu____11667 :: g  in
                let uu____11671 =
                  let uu____11674 =
                    let uu____11675 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11675  in
                  [uu____11674]  in
                FStar_List.append uu____11664 uu____11671
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
        let uu____11691 =
          let uu____11692 = FStar_Syntax_Subst.compress t  in
          uu____11692.FStar_Syntax_Syntax.n  in
        match uu____11691 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11697)) -> s = "opaque_to_smt"
        | uu____11702 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11711 =
          let uu____11712 = FStar_Syntax_Subst.compress t  in
          uu____11712.FStar_Syntax_Syntax.n  in
        match uu____11711 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11717)) -> s = "uninterpreted_by_smt"
        | uu____11722 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11728 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11734 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____11746 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____11747 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11748 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11761 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11763 =
            let uu____11765 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____11765  in
          if uu____11763
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11794 ->
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
               let uu____11826 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11826 with
               | (formals,uu____11846) ->
                   let arity = FStar_List.length formals  in
                   let uu____11870 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11870 with
                    | (aname,atok,env2) ->
                        let uu____11896 =
                          let uu____11901 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11901 env2
                           in
                        (match uu____11896 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11913 =
                                 let uu____11914 =
                                   let uu____11926 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____11946  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11926,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11914
                                  in
                               [uu____11913;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____11963 =
                               let aux uu____12024 uu____12025 =
                                 match (uu____12024, uu____12025) with
                                 | ((bv,uu____12084),(env3,acc_sorts,acc)) ->
                                     let uu____12131 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____12131 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____11963 with
                              | (uu____12215,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____12241 =
                                      let uu____12249 =
                                        let uu____12250 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12251 =
                                          let uu____12262 =
                                            let uu____12263 =
                                              let uu____12268 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____12268)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12263
                                             in
                                          ([[app]], xs_sorts, uu____12262)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12250 uu____12251
                                         in
                                      (uu____12249,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12241
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
                                    let uu____12285 =
                                      let uu____12293 =
                                        let uu____12294 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12295 =
                                          let uu____12306 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12306)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12294 uu____12295
                                         in
                                      (uu____12293,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12285
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12321 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12321 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12347,uu____12348)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12349 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12349 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12371,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12378 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___431_12384  ->
                      match uu___431_12384 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12387 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12393 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12396 -> false))
               in
            Prims.op_Negation uu____12378  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12406 =
               let uu____12413 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12413 env fv t quals  in
             match uu____12406 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12432 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12432 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12452 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12452 with
           | (uvs,f1) ->
               let env1 =
                 let uu___449_12464 = env  in
                 let uu____12465 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___449_12464.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___449_12464.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___449_12464.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12465;
                   FStar_SMTEncoding_Env.warn =
                     (uu___449_12464.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___449_12464.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___449_12464.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___449_12464.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___449_12464.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___449_12464.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___449_12464.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12467 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12467 with
                | (f3,decls) ->
                    let g =
                      let uu____12481 =
                        let uu____12482 =
                          let uu____12490 =
                            let uu____12491 =
                              let uu____12493 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12493
                               in
                            FStar_Pervasives_Native.Some uu____12491  in
                          let uu____12497 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12490, uu____12497)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12482  in
                      [uu____12481]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12502) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12516 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12538 =
                       let uu____12541 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12541.FStar_Syntax_Syntax.fv_name  in
                     uu____12538.FStar_Syntax_Syntax.v  in
                   let uu____12542 =
                     let uu____12544 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12544  in
                   if uu____12542
                   then
                     let val_decl =
                       let uu___450_12576 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___450_12576.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___450_12576.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___450_12576.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12577 = encode_sigelt' env1 val_decl  in
                     match uu____12577 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12516 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12613,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12615;
                          FStar_Syntax_Syntax.lbtyp = uu____12616;
                          FStar_Syntax_Syntax.lbeff = uu____12617;
                          FStar_Syntax_Syntax.lbdef = uu____12618;
                          FStar_Syntax_Syntax.lbattrs = uu____12619;
                          FStar_Syntax_Syntax.lbpos = uu____12620;_}::[]),uu____12621)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12640 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12640 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12683 =
                   let uu____12686 =
                     let uu____12687 =
                       let uu____12695 =
                         let uu____12696 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12697 =
                           let uu____12708 =
                             let uu____12709 =
                               let uu____12714 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12714)  in
                             FStar_SMTEncoding_Util.mkEq uu____12709  in
                           ([[b2t_x]], [xx], uu____12708)  in
                         FStar_SMTEncoding_Term.mkForall uu____12696
                           uu____12697
                          in
                       (uu____12695,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12687  in
                   [uu____12686]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12683
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____12746,uu____12747) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___432_12757  ->
                  match uu___432_12757 with
                  | FStar_Syntax_Syntax.Discriminator uu____12759 -> true
                  | uu____12761 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____12763,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____12775 =
                     let uu____12777 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____12777.FStar_Ident.idText  in
                   uu____12775 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___433_12784  ->
                     match uu___433_12784 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12787 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12790) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___434_12804  ->
                  match uu___434_12804 with
                  | FStar_Syntax_Syntax.Projector uu____12806 -> true
                  | uu____12812 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12816 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12816 with
           | FStar_Pervasives_Native.Some uu____12823 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___451_12825 = se  in
                 let uu____12826 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12826;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___451_12825.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___451_12825.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___451_12825.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12829) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12844) ->
          let uu____12853 = encode_sigelts env ses  in
          (match uu____12853 with
           | (g,env1) ->
               let uu____12870 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___435_12893  ->
                         match uu___435_12893 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12895;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12896;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12897;_}
                             -> false
                         | uu____12904 -> true))
                  in
               (match uu____12870 with
                | (g',inversions) ->
                    let uu____12920 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___436_12941  ->
                              match uu___436_12941 with
                              | FStar_SMTEncoding_Term.DeclFun uu____12943 ->
                                  true
                              | uu____12956 -> false))
                       in
                    (match uu____12920 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12973,tps,k,uu____12976,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___437_12995  ->
                    match uu___437_12995 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12999 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13012 = c  in
              match uu____13012 with
              | (name,args,uu____13017,uu____13018,uu____13019) ->
                  let uu____13030 =
                    let uu____13031 =
                      let uu____13043 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13070  ->
                                match uu____13070 with
                                | (uu____13079,sort,uu____13081) -> sort))
                         in
                      (name, uu____13043, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13031  in
                  [uu____13030]
            else
              (let uu____13092 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____13092 c)
             in
          let inversion_axioms tapp vars =
            let uu____13120 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13128 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____13128 FStar_Option.isNone))
               in
            if uu____13120
            then []
            else
              (let uu____13163 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____13163 with
               | (xxsym,xx) ->
                   let uu____13176 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13215  ->
                             fun l  ->
                               match uu____13215 with
                               | (out,decls) ->
                                   let uu____13235 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____13235 with
                                    | (uu____13246,data_t) ->
                                        let uu____13248 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13248 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13292 =
                                                 let uu____13293 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13293.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13292 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13296,indices) ->
                                                   indices
                                               | uu____13322 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13352  ->
                                                         match uu____13352
                                                         with
                                                         | (x,uu____13360) ->
                                                             let uu____13365
                                                               =
                                                               let uu____13366
                                                                 =
                                                                 let uu____13374
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13374,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13366
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13365)
                                                    env)
                                                in
                                             let uu____13379 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13379 with
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
                                                      let uu____13409 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13427
                                                                 =
                                                                 let uu____13432
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13432,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13427)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13409
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13435 =
                                                      let uu____13436 =
                                                        let uu____13441 =
                                                          let uu____13442 =
                                                            let uu____13447 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13447,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13442
                                                           in
                                                        (out, uu____13441)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13436
                                                       in
                                                    (uu____13435,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13176 with
                    | (data_ax,decls) ->
                        let uu____13460 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13460 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13477 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13477 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13484 =
                                 let uu____13492 =
                                   let uu____13493 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13494 =
                                     let uu____13505 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13518 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13505,
                                       uu____13518)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13493 uu____13494
                                    in
                                 let uu____13527 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13492,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13527)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13484
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13533 =
            let uu____13538 =
              let uu____13539 = FStar_Syntax_Subst.compress k  in
              uu____13539.FStar_Syntax_Syntax.n  in
            match uu____13538 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13574 -> (tps, k)  in
          (match uu____13533 with
           | (formals,res) ->
               let uu____13581 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13581 with
                | (formals1,res1) ->
                    let uu____13592 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13592 with
                     | (vars,guards,env',binder_decls,uu____13617) ->
                         let arity = FStar_List.length vars  in
                         let uu____13631 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13631 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13661 =
                                  let uu____13669 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13669)  in
                                FStar_SMTEncoding_Util.mkApp uu____13661  in
                              let uu____13675 =
                                let tname_decl =
                                  let uu____13685 =
                                    let uu____13686 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13714  ->
                                              match uu____13714 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13735 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13686,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13735, false)
                                     in
                                  constructor_or_logic_type_decl uu____13685
                                   in
                                let uu____13743 =
                                  match vars with
                                  | [] ->
                                      let uu____13756 =
                                        let uu____13757 =
                                          let uu____13760 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____13760
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____13757
                                         in
                                      ([], uu____13756)
                                  | uu____13772 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13782 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13782
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13798 =
                                          let uu____13806 =
                                            let uu____13807 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13808 =
                                              let uu____13824 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13824)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13807 uu____13808
                                             in
                                          (uu____13806,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13798
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13743 with
                                | (tok_decls,env2) ->
                                    let uu____13851 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13851
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13675 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13879 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13879 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13901 =
                                               let uu____13902 =
                                                 let uu____13910 =
                                                   let uu____13911 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13911
                                                    in
                                                 (uu____13910,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13902
                                                in
                                             [uu____13901]
                                           else []  in
                                         let uu____13919 =
                                           let uu____13922 =
                                             let uu____13925 =
                                               let uu____13926 =
                                                 let uu____13934 =
                                                   let uu____13935 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____13936 =
                                                     let uu____13947 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13947)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____13935 uu____13936
                                                    in
                                                 (uu____13934,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13926
                                                in
                                             [uu____13925]  in
                                           FStar_List.append karr uu____13922
                                            in
                                         FStar_List.append decls1 uu____13919
                                      in
                                   let aux =
                                     let uu____13962 =
                                       let uu____13965 =
                                         inversion_axioms tapp vars  in
                                       let uu____13968 =
                                         let uu____13971 =
                                           let uu____13972 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____13972 env2
                                             tapp vars
                                            in
                                         [uu____13971]  in
                                       FStar_List.append uu____13965
                                         uu____13968
                                        in
                                     FStar_List.append kindingAx uu____13962
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13977,uu____13978,uu____13979,uu____13980,uu____13981)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13989,t,uu____13991,n_tps,uu____13993) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____14003 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____14003 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____14051 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____14051 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____14079 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____14079 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14099 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____14099 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14178 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____14178,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14185 =
                                  let uu____14186 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14186, true)
                                   in
                                let uu____14194 =
                                  let uu____14201 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____14201
                                   in
                                FStar_All.pipe_right uu____14185 uu____14194
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
                              let uu____14213 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____14213 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14225::uu____14226 ->
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
                                         let uu____14285 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____14286 =
                                           let uu____14297 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14297)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____14285 uu____14286
                                     | uu____14318 -> tok_typing  in
                                   let uu____14329 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14329 with
                                    | (vars',guards',env'',decls_formals,uu____14354)
                                        ->
                                        let uu____14367 =
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
                                        (match uu____14367 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14397 ->
                                                   let uu____14406 =
                                                     let uu____14407 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14407
                                                      in
                                                   [uu____14406]
                                                in
                                             let encode_elim uu____14423 =
                                               let uu____14424 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14424 with
                                               | (head1,args) ->
                                                   let uu____14475 =
                                                     let uu____14476 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14476.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14475 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14488;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14489;_},uu____14490)
                                                        ->
                                                        let uu____14495 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14495
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14516
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14516
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
                                                                    uu____14570
                                                                    ->
                                                                    let uu____14571
                                                                    =
                                                                    let uu____14577
                                                                    =
                                                                    let uu____14579
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14579
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14577)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14571
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14599
                                                                    =
                                                                    let uu____14601
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14601
                                                                     in
                                                                    if
                                                                    uu____14599
                                                                    then
                                                                    let uu____14617
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14617]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14620
                                                                    =
                                                                    let uu____14634
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14691
                                                                     ->
                                                                    fun
                                                                    uu____14692
                                                                     ->
                                                                    match 
                                                                    (uu____14691,
                                                                    uu____14692)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14803
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14811
                                                                     in
                                                                    (match uu____14803
                                                                    with
                                                                    | 
                                                                    (uu____14825,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14836
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14836
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14841
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14841
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
                                                                    uu____14634
                                                                     in
                                                                  (match uu____14620
                                                                   with
                                                                   | 
                                                                   (uu____14862,arg_vars,elim_eqns_or_guards,uu____14865)
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
                                                                    let uu____14892
                                                                    =
                                                                    let uu____14900
                                                                    =
                                                                    let uu____14901
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14902
                                                                    =
                                                                    let uu____14913
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14915
                                                                    =
                                                                    let uu____14916
                                                                    =
                                                                    let uu____14921
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14921)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14916
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14913,
                                                                    uu____14915)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14901
                                                                    uu____14902
                                                                     in
                                                                    (uu____14900,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14892
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    let uu____14942
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14942,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14936
                                                                     in
                                                                    let uu____14945
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14945
                                                                    then
                                                                    let x =
                                                                    let uu____14954
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14954,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14959
                                                                    =
                                                                    let uu____14967
                                                                    =
                                                                    let uu____14968
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14969
                                                                    =
                                                                    let uu____14980
                                                                    =
                                                                    let uu____14985
                                                                    =
                                                                    let uu____14988
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14988]
                                                                     in
                                                                    [uu____14985]
                                                                     in
                                                                    let uu____14993
                                                                    =
                                                                    let uu____14994
                                                                    =
                                                                    let uu____14999
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14999,
                                                                    uu____15001)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14994
                                                                     in
                                                                    (uu____14980,
                                                                    [x],
                                                                    uu____14993)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14968
                                                                    uu____14969
                                                                     in
                                                                    let uu____15016
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14967,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15016)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14959
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15027
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
                                                                    (let uu____15065
                                                                    =
                                                                    let uu____15066
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15066
                                                                    dapp1  in
                                                                    [uu____15065])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15027
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15073
                                                                    =
                                                                    let uu____15081
                                                                    =
                                                                    let uu____15082
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15083
                                                                    =
                                                                    let uu____15094
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15096
                                                                    =
                                                                    let uu____15097
                                                                    =
                                                                    let uu____15102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15102)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15097
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15094,
                                                                    uu____15096)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15082
                                                                    uu____15083
                                                                     in
                                                                    (uu____15081,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15073)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____15120 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____15120
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____15141
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____15141
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
                                                                    uu____15195
                                                                    ->
                                                                    let uu____15196
                                                                    =
                                                                    let uu____15202
                                                                    =
                                                                    let uu____15204
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15204
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15202)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15196
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15224
                                                                    =
                                                                    let uu____15226
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15226
                                                                     in
                                                                    if
                                                                    uu____15224
                                                                    then
                                                                    let uu____15242
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15242]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____15245
                                                                    =
                                                                    let uu____15259
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15316
                                                                     ->
                                                                    fun
                                                                    uu____15317
                                                                     ->
                                                                    match 
                                                                    (uu____15316,
                                                                    uu____15317)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15428
                                                                    =
                                                                    let uu____15436
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15436
                                                                     in
                                                                    (match uu____15428
                                                                    with
                                                                    | 
                                                                    (uu____15450,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15461
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15461
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15466
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15466
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
                                                                    uu____15259
                                                                     in
                                                                  (match uu____15245
                                                                   with
                                                                   | 
                                                                   (uu____15487,arg_vars,elim_eqns_or_guards,uu____15490)
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
                                                                    let uu____15517
                                                                    =
                                                                    let uu____15525
                                                                    =
                                                                    let uu____15526
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15527
                                                                    =
                                                                    let uu____15538
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15540
                                                                    =
                                                                    let uu____15541
                                                                    =
                                                                    let uu____15546
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15546)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15541
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15538,
                                                                    uu____15540)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15526
                                                                    uu____15527
                                                                     in
                                                                    (uu____15525,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15517
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15561
                                                                    =
                                                                    let uu____15567
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15567,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15561
                                                                     in
                                                                    let uu____15570
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15570
                                                                    then
                                                                    let x =
                                                                    let uu____15579
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15579,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15584
                                                                    =
                                                                    let uu____15592
                                                                    =
                                                                    let uu____15593
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15594
                                                                    =
                                                                    let uu____15605
                                                                    =
                                                                    let uu____15610
                                                                    =
                                                                    let uu____15613
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15613]
                                                                     in
                                                                    [uu____15610]
                                                                     in
                                                                    let uu____15618
                                                                    =
                                                                    let uu____15619
                                                                    =
                                                                    let uu____15624
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15626
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15624,
                                                                    uu____15626)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15619
                                                                     in
                                                                    (uu____15605,
                                                                    [x],
                                                                    uu____15618)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15593
                                                                    uu____15594
                                                                     in
                                                                    let uu____15641
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15592,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15641)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15584
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15652
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
                                                                    (let uu____15690
                                                                    =
                                                                    let uu____15691
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15691
                                                                    dapp1  in
                                                                    [uu____15690])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15652
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15698
                                                                    =
                                                                    let uu____15706
                                                                    =
                                                                    let uu____15707
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15708
                                                                    =
                                                                    let uu____15719
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15721
                                                                    =
                                                                    let uu____15722
                                                                    =
                                                                    let uu____15727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15722
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15719,
                                                                    uu____15721)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15707
                                                                    uu____15708
                                                                     in
                                                                    (uu____15706,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15698)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15744 ->
                                                        ((let uu____15746 =
                                                            let uu____15752 =
                                                              let uu____15754
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____15756
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____15754
                                                                uu____15756
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____15752)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15746);
                                                         ([], [])))
                                                in
                                             let uu____15764 = encode_elim ()
                                                in
                                             (match uu____15764 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15790 =
                                                      let uu____15793 =
                                                        let uu____15796 =
                                                          let uu____15799 =
                                                            let uu____15802 =
                                                              let uu____15803
                                                                =
                                                                let uu____15815
                                                                  =
                                                                  let uu____15816
                                                                    =
                                                                    let uu____15818
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15818
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15816
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15815)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15803
                                                               in
                                                            [uu____15802]  in
                                                          let uu____15825 =
                                                            let uu____15828 =
                                                              let uu____15831
                                                                =
                                                                let uu____15834
                                                                  =
                                                                  let uu____15837
                                                                    =
                                                                    let uu____15840
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15845
                                                                    =
                                                                    let uu____15848
                                                                    =
                                                                    let uu____15849
                                                                    =
                                                                    let uu____15857
                                                                    =
                                                                    let uu____15858
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15859
                                                                    =
                                                                    let uu____15870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15870)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15858
                                                                    uu____15859
                                                                     in
                                                                    (uu____15857,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15849
                                                                     in
                                                                    let uu____15883
                                                                    =
                                                                    let uu____15886
                                                                    =
                                                                    let uu____15887
                                                                    =
                                                                    let uu____15895
                                                                    =
                                                                    let uu____15896
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15897
                                                                    =
                                                                    let uu____15908
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15910
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15908,
                                                                    uu____15910)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15896
                                                                    uu____15897
                                                                     in
                                                                    (uu____15895,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15887
                                                                     in
                                                                    [uu____15886]
                                                                     in
                                                                    uu____15848
                                                                    ::
                                                                    uu____15883
                                                                     in
                                                                    uu____15840
                                                                    ::
                                                                    uu____15845
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15837
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15834
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15831
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15828
                                                             in
                                                          FStar_List.append
                                                            uu____15799
                                                            uu____15825
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15796
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15793
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15790
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
           (fun uu____15948  ->
              fun se  ->
                match uu____15948 with
                | (g,env1) ->
                    let uu____15968 = encode_sigelt env1 se  in
                    (match uu____15968 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16036 =
        match uu____16036 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____16073 ->
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
                 ((let uu____16081 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____16081
                   then
                     let uu____16086 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____16088 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____16090 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16086 uu____16088 uu____16090
                   else ());
                  (let uu____16095 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____16095 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____16113 =
                         let uu____16121 =
                           let uu____16123 =
                             let uu____16125 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16125
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16123  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16121
                          in
                       (match uu____16113 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16145 = FStar_Options.log_queries ()
                                 in
                              if uu____16145
                              then
                                let uu____16148 =
                                  let uu____16150 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16152 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16154 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16150 uu____16152 uu____16154
                                   in
                                FStar_Pervasives_Native.Some uu____16148
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16178,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16198 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16198 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16225 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16225 with | (uu____16252,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____16268 'Auu____16269 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____16268 *
      'Auu____16269) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16342  ->
              match uu____16342 with
              | (l,uu____16355,uu____16356) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16407  ->
              match uu____16407 with
              | (l,uu____16422,uu____16423) ->
                  let uu____16434 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16437 =
                    let uu____16440 =
                      let uu____16441 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16441  in
                    [uu____16440]  in
                  uu____16434 :: uu____16437))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16470 =
      let uu____16473 =
        let uu____16474 = FStar_Util.psmap_empty ()  in
        let uu____16489 = FStar_Util.psmap_empty ()  in
        let uu____16492 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16496 =
          let uu____16498 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16498 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16474;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16489;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16492;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16496;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16473]  in
    FStar_ST.op_Colon_Equals last_env uu____16470
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16540 = FStar_ST.op_Bang last_env  in
      match uu____16540 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16568 ->
          let uu___452_16571 = e  in
          let uu____16572 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___452_16571.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___452_16571.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___452_16571.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___452_16571.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___452_16571.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___452_16571.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___452_16571.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___452_16571.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16572;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___452_16571.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16580 = FStar_ST.op_Bang last_env  in
    match uu____16580 with
    | [] -> failwith "Empty env stack"
    | uu____16607::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16639  ->
    let uu____16640 = FStar_ST.op_Bang last_env  in
    match uu____16640 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16700  ->
    let uu____16701 = FStar_ST.op_Bang last_env  in
    match uu____16701 with
    | [] -> failwith "Popping an empty stack"
    | uu____16728::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16765  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16818  ->
         let uu____16819 = snapshot_env ()  in
         match uu____16819 with
         | (env_depth,()) ->
             let uu____16841 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16841 with
              | (varops_depth,()) ->
                  let uu____16863 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16863 with
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
        (fun uu____16921  ->
           let uu____16922 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16922 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____17017 = snapshot msg  in () 
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
        | (uu____17063::uu____17064,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___453_17072 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___453_17072.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___453_17072.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___453_17072.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17073 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____17093 =
        let uu____17096 =
          let uu____17097 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____17097  in
        let uu____17098 = open_fact_db_tags env  in uu____17096 ::
          uu____17098
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17093
  
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
      let uu____17125 = encode_sigelt env se  in
      match uu____17125 with
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
        let uu____17170 = FStar_Options.log_queries ()  in
        if uu____17170
        then
          let uu____17175 =
            let uu____17176 =
              let uu____17178 =
                let uu____17180 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17180 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17178  in
            FStar_SMTEncoding_Term.Caption uu____17176  in
          uu____17175 :: decls
        else decls  in
      (let uu____17199 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____17199
       then
         let uu____17202 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17202
       else ());
      (let env =
         let uu____17208 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17208 tcenv  in
       let uu____17209 = encode_top_level_facts env se  in
       match uu____17209 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17223 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17223)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17237 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17237
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17252 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____17252
          then
            let uu____17255 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17255
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17301  ->
                    fun se  ->
                      match uu____17301 with
                      | (g,env2) ->
                          let uu____17321 = encode_top_level_facts env2 se
                             in
                          (match uu____17321 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17344 =
            encode_signature
              (let uu___454_17353 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___454_17353.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___454_17353.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___454_17353.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___454_17353.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___454_17353.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___454_17353.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___454_17353.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___454_17353.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___454_17353.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___454_17353.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17344 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17373 = FStar_Options.log_queries ()  in
                if uu____17373
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
                 (let uu___455_17390 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___455_17390.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___455_17390.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___455_17390.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___455_17390.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___455_17390.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___455_17390.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___455_17390.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___455_17390.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___455_17390.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___455_17390.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17393 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17393
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
        (let uu____17458 =
           let uu____17460 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17460.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17458);
        (let env =
           let uu____17462 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17462 tcenv  in
         let uu____17463 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17502 = aux rest  in
                 (match uu____17502 with
                  | (out,rest1) ->
                      let t =
                        let uu____17530 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17530 with
                        | FStar_Pervasives_Native.Some uu____17533 ->
                            let uu____17534 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17534
                              x.FStar_Syntax_Syntax.sort
                        | uu____17535 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17539 =
                        let uu____17542 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___456_17545 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___456_17545.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___456_17545.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17542 :: out  in
                      (uu____17539, rest1))
             | uu____17550 -> ([], bindings)  in
           let uu____17557 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17557 with
           | (closing,bindings) ->
               let uu____17584 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17584, bindings)
            in
         match uu____17463 with
         | (q1,bindings) ->
             let uu____17615 = encode_env_bindings env bindings  in
             (match uu____17615 with
              | (env_decls,env1) ->
                  ((let uu____17637 =
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
                    if uu____17637
                    then
                      let uu____17644 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17644
                    else ());
                   (let uu____17649 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17649 with
                    | (phi,qdecls) ->
                        let uu____17670 =
                          let uu____17675 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17675 phi
                           in
                        (match uu____17670 with
                         | (labels,phi1) ->
                             let uu____17692 = encode_labels labels  in
                             (match uu____17692 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17729 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17729
                                    then
                                      let uu____17734 =
                                        let uu____17735 =
                                          let uu____17737 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17737
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17735
                                         in
                                      [uu____17734]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17746 =
                                      let uu____17754 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17755 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17754,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17755)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17746
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
  