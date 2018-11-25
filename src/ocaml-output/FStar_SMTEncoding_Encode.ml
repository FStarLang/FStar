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
  let squash env t =
    let sq =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.squash_lid  in
    let b2t1 =
      FStar_SMTEncoding_Env.lookup_lid env FStar_Parser_Const.b2t_lid  in
    let uu____3957 =
      let uu____3965 =
        let uu____3968 =
          let uu____3969 =
            let uu____3977 =
              let uu____3980 = FStar_SMTEncoding_Term.boxBool t  in
              [uu____3980]  in
            ((b2t1.FStar_SMTEncoding_Env.smt_id), uu____3977)  in
          FStar_SMTEncoding_Util.mkApp uu____3969  in
        [uu____3968]  in
      ((sq.FStar_SMTEncoding_Env.smt_id), uu____3965)  in
    FStar_SMTEncoding_Util.mkApp uu____3957  in
  let bind_macro env lid macro_name =
    let fvb = FStar_SMTEncoding_Env.lookup_lid env lid  in
    FStar_SMTEncoding_Env.push_free_var env lid
      fvb.FStar_SMTEncoding_Env.smt_arity macro_name
      fvb.FStar_SMTEncoding_Env.smt_token
     in
  let mk_unary_prop_connective conn interp env vname uu____4039 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let conn_a = FStar_SMTEncoding_Util.mkApp (vname, [a])  in
    let valid_conn_a = mkValid conn_a  in
    let valid_a = mkValid a  in
    let macro_name = mk_macro_name vname  in
    let macro =
      let uu____4065 =
        let uu____4084 =
          let uu____4085 = interp valid_a  in squash env uu____4085  in
        (macro_name, [aa], FStar_SMTEncoding_Term.Term_sort, uu____4084,
          (FStar_Pervasives_Native.Some "macro for embedded unary connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4065  in
    let uu____4106 =
      let uu____4107 =
        let uu____4108 =
          let uu____4116 =
            let uu____4117 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4118 =
              let uu____4129 =
                let uu____4130 =
                  let uu____4135 = interp valid_a  in
                  (uu____4135, valid_conn_a)  in
                FStar_SMTEncoding_Util.mkIff uu____4130  in
              ([[conn_a]], [aa], uu____4129)  in
            FStar_SMTEncoding_Term.mkForall uu____4117 uu____4118  in
          (uu____4116,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4108  in
      [uu____4107; macro]  in
    let uu____4158 = bind_macro env conn macro_name  in
    (uu____4106, uu____4158)  in
  let mk_binary_prop_connective conn interp env vname uu____4196 =
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
      let uu____4236 =
        let uu____4255 =
          let uu____4256 = interp (valid_a, valid_b)  in
          squash env uu____4256  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4255,
          (FStar_Pervasives_Native.Some "macro for embedded connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4236  in
    let uu____4282 =
      let uu____4283 =
        let uu____4284 =
          let uu____4292 =
            let uu____4293 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4294 =
              let uu____4305 =
                let uu____4306 =
                  let uu____4311 = interp (valid_a, valid_b)  in
                  (uu____4311, valid_conn_a_b)  in
                FStar_SMTEncoding_Util.mkIff uu____4306  in
              ([[conn_a_b]], [aa; bb], uu____4305)  in
            FStar_SMTEncoding_Term.mkForall uu____4293 uu____4294  in
          (uu____4292,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4284  in
      [uu____4283; macro]  in
    let uu____4339 = bind_macro env conn macro_name  in
    (uu____4282, uu____4339)  in
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
    let uu____4484 =
      let uu____4485 =
        let uu____4493 =
          let uu____4494 = FStar_TypeChecker_Env.get_range env  in
          let uu____4495 =
            let uu____4506 =
              let uu____4507 =
                let uu____4512 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4512, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4507  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4506)  in
          FStar_SMTEncoding_Term.mkForall uu____4494 uu____4495  in
        (uu____4493, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4485  in
    [uu____4484]  in
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
    let uu____4608 =
      let uu____4609 =
        let uu____4617 =
          let uu____4618 = FStar_TypeChecker_Env.get_range env  in
          let uu____4619 =
            let uu____4630 =
              let uu____4631 =
                let uu____4636 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4636, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4631  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4630)  in
          FStar_SMTEncoding_Term.mkForall uu____4618 uu____4619  in
        (uu____4617, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4609  in
    [uu____4608]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4696 =
      let uu____4697 =
        let uu____4705 =
          let uu____4706 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4706 range_ty  in
        let uu____4707 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4705, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4707)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4697  in
    [uu____4696]  in
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
        let uu____4761 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4761 x1 t  in
      let uu____4763 = FStar_TypeChecker_Env.get_range env  in
      let uu____4764 =
        let uu____4775 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4775)  in
      FStar_SMTEncoding_Term.mkForall uu____4763 uu____4764  in
    let uu____4794 =
      let uu____4795 =
        let uu____4803 =
          let uu____4804 = FStar_TypeChecker_Env.get_range env  in
          let uu____4805 =
            let uu____4816 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4816)  in
          FStar_SMTEncoding_Term.mkForall uu____4804 uu____4805  in
        (uu____4803,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4795  in
    [uu____4794]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4879 =
      let uu____4880 =
        let uu____4888 =
          let uu____4889 = FStar_TypeChecker_Env.get_range env  in
          let uu____4890 =
            let uu____4906 =
              let uu____4907 =
                let uu____4912 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4913 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4912, uu____4913)  in
              FStar_SMTEncoding_Util.mkAnd uu____4907  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4906)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4889 uu____4890  in
        (uu____4888,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4880  in
    [uu____4879]  in
  let mk_squash_interp env sq uu____4962 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_sq_a =
      let uu____4979 =
        let uu____4987 =
          let uu____4990 = FStar_SMTEncoding_Util.mkApp (sq, [a])  in
          [uu____4990]  in
        ("Valid", uu____4987)  in
      FStar_SMTEncoding_Util.mkApp uu____4979  in
    let uu____4998 =
      let uu____4999 =
        let uu____5007 =
          let uu____5008 = FStar_TypeChecker_Env.get_range env  in
          let uu____5009 =
            let uu____5020 =
              FStar_SMTEncoding_Util.mkIff (valid_sq_a, valid_a)  in
            ([[valid_sq_a]], [aa], uu____5020)  in
          FStar_SMTEncoding_Term.mkForall uu____5008 uu____5009  in
        (uu____5007,
          (FStar_Pervasives_Native.Some "valid-squash interpretation"),
          "valid-squash-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4999  in
    [uu____4998]  in
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
          let uu____5703 =
            FStar_Util.find_opt
              (fun uu____5749  ->
                 match uu____5749 with
                 | (l,uu____5769) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5703 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____5830,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5903 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5903 with
        | (form,decls) ->
            let uu____5912 =
              let uu____5915 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5915]  in
            FStar_List.append decls uu____5912
  
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
              let uu____5972 =
                ((let uu____5976 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5976) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5972
              then
                let arg_sorts =
                  let uu____5990 =
                    let uu____5991 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5991.FStar_Syntax_Syntax.n  in
                  match uu____5990 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5997) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6035  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6042 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____6044 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____6044 with
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
                (let uu____6086 = prims.is lid  in
                 if uu____6086
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____6097 = prims.mk lid vname  in
                   match uu____6097 with
                   | (vname1,tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname1 (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6137 =
                      let uu____6156 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6156 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6184 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6184
                            then
                              let uu____6189 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___380_6192 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___380_6192.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___380_6192.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___380_6192.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___380_6192.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___380_6192.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___380_6192.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___380_6192.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___380_6192.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___380_6192.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___380_6192.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___380_6192.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___380_6192.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___380_6192.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___380_6192.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___380_6192.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___380_6192.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___380_6192.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___380_6192.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___380_6192.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___380_6192.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___380_6192.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___380_6192.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___380_6192.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___380_6192.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___380_6192.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___380_6192.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___380_6192.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___380_6192.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___380_6192.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___380_6192.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___380_6192.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___380_6192.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___380_6192.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___380_6192.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___380_6192.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___380_6192.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___380_6192.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___380_6192.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___380_6192.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___380_6192.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___380_6192.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___380_6192.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6189
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6215 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6215)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6137 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6296 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6296 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6330 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___370_6391  ->
                                       match uu___370_6391 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6395 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6395 with
                                            | (uu____6419,(xxsym,uu____6421))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6445 =
                                                  let uu____6446 =
                                                    let uu____6454 =
                                                      let uu____6455 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6456 =
                                                        let uu____6467 =
                                                          let uu____6468 =
                                                            let uu____6473 =
                                                              let uu____6474
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6474
                                                               in
                                                            (vapp,
                                                              uu____6473)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6468
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6467)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6455 uu____6456
                                                       in
                                                    (uu____6454,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6446
                                                   in
                                                [uu____6445])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6489 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6489 with
                                            | (uu____6513,(xxsym,uu____6515))
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
                                                let uu____6547 =
                                                  let uu____6548 =
                                                    let uu____6556 =
                                                      let uu____6557 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6558 =
                                                        let uu____6569 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6569)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6557 uu____6558
                                                       in
                                                    (uu____6556,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6548
                                                   in
                                                [uu____6547])
                                       | uu____6582 -> []))
                                in
                             let uu____6583 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6583 with
                              | (vars,guards,env',decls1,uu____6610) ->
                                  let uu____6623 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6636 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6636, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6640 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6640 with
                                         | (g,ds) ->
                                             let uu____6653 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6653,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6623 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6670 =
                                           let uu____6678 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6678)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6670
                                          in
                                       let uu____6684 =
                                         let vname_decl =
                                           let uu____6692 =
                                             let uu____6704 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6724  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6704,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6692
                                            in
                                         let uu____6735 =
                                           let env2 =
                                             let uu___381_6741 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___381_6741.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____6742 =
                                             let uu____6744 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6744  in
                                           if uu____6742
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6735 with
                                         | (tok_typing,decls2) ->
                                             let uu____6761 =
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
                                                   let uu____6785 =
                                                     let uu____6786 =
                                                       let uu____6789 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6789
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6786
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6785)
                                               | uu____6799 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6814 =
                                                       let uu____6822 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6822]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6814
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6844 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6845 =
                                                       let uu____6856 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6856)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6844 uu____6845
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6866 =
                                                       let uu____6874 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6874,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6866
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
                                                       let uu____6913 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6914 =
                                                         let uu____6925 =
                                                           let uu____6926 =
                                                             let uu____6931 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6932 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6931,
                                                               uu____6932)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6926
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6925)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6913
                                                         uu____6914
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
                                             (match uu____6761 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6684 with
                                        | (decls2,env2) ->
                                            let uu____6983 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____6993 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____6993 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____7008 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____7008,
                                                    decls)
                                               in
                                            (match uu____6983 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____7025 =
                                                     let uu____7033 =
                                                       let uu____7034 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7035 =
                                                         let uu____7046 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____7046)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7034
                                                         uu____7035
                                                        in
                                                     (uu____7033,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7025
                                                    in
                                                 let freshness =
                                                   let uu____7062 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____7062
                                                   then
                                                     let uu____7070 =
                                                       let uu____7071 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____7072 =
                                                         let uu____7085 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____7103 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____7085,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____7103)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____7071
                                                         uu____7072
                                                        in
                                                     let uu____7109 =
                                                       let uu____7112 =
                                                         let uu____7113 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____7113 env2
                                                           vapp vars
                                                          in
                                                       [uu____7112]  in
                                                     uu____7070 :: uu____7109
                                                   else []  in
                                                 let g =
                                                   let uu____7119 =
                                                     let uu____7122 =
                                                       let uu____7125 =
                                                         let uu____7128 =
                                                           let uu____7131 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____7131
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____7128
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____7125
                                                        in
                                                     FStar_List.append decls2
                                                       uu____7122
                                                      in
                                                   FStar_List.append decls11
                                                     uu____7119
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
          let uu____7173 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7173 with
          | FStar_Pervasives_Native.None  ->
              let uu____7184 = encode_free_var false env x t t_norm []  in
              (match uu____7184 with
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
            let uu____7255 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7255 with
            | (decls,env1) ->
                let uu____7274 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7274
                then
                  let uu____7283 =
                    let uu____7286 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7286  in
                  (uu____7283, env1)
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
             (fun uu____7346  ->
                fun lb  ->
                  match uu____7346 with
                  | (decls,env1) ->
                      let uu____7366 =
                        let uu____7373 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7373
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7366 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7406 = FStar_Syntax_Util.head_and_args t  in
    match uu____7406 with
    | (hd1,args) ->
        let uu____7450 =
          let uu____7451 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7451.FStar_Syntax_Syntax.n  in
        (match uu____7450 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7457,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7481 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7492 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___382_7500 = en  in
    let uu____7501 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___382_7500.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___382_7500.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___382_7500.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___382_7500.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___382_7500.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7501;
      FStar_SMTEncoding_Env.nolabels =
        (uu___382_7500.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___382_7500.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___382_7500.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___382_7500.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___382_7500.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7533  ->
      fun quals  ->
        match uu____7533 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7640 = FStar_Util.first_N nbinders formals  in
              match uu____7640 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7741  ->
                         fun uu____7742  ->
                           match (uu____7741, uu____7742) with
                           | ((formal,uu____7768),(binder,uu____7770)) ->
                               let uu____7791 =
                                 let uu____7798 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7798)  in
                               FStar_Syntax_Syntax.NT uu____7791) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7812 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7853  ->
                              match uu____7853 with
                              | (x,i) ->
                                  let uu____7872 =
                                    let uu___383_7873 = x  in
                                    let uu____7874 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_7873.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_7873.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7874
                                    }  in
                                  (uu____7872, i)))
                       in
                    FStar_All.pipe_right uu____7812
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7898 =
                      let uu____7903 = FStar_Syntax_Subst.compress body  in
                      let uu____7904 =
                        let uu____7905 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7905
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7903 uu____7904
                       in
                    uu____7898 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____7990 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____7990
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___384_7997 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___384_7997.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___384_7997.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___384_7997.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___384_7997.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___384_7997.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___384_7997.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___384_7997.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___384_7997.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___384_7997.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___384_7997.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___384_7997.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___384_7997.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___384_7997.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___384_7997.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___384_7997.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___384_7997.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___384_7997.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___384_7997.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___384_7997.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___384_7997.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___384_7997.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___384_7997.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___384_7997.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___384_7997.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___384_7997.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___384_7997.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___384_7997.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___384_7997.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___384_7997.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___384_7997.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___384_7997.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___384_7997.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___384_7997.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___384_7997.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___384_7997.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___384_7997.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___384_7997.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___384_7997.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___384_7997.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___384_7997.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___384_7997.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___384_7997.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____8047 = FStar_Syntax_Util.abs_formals e  in
                match uu____8047 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8129::uu____8130 ->
                         let uu____8151 =
                           let uu____8152 =
                             let uu____8155 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____8155
                              in
                           uu____8152.FStar_Syntax_Syntax.n  in
                         (match uu____8151 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8213 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8213 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____8270 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____8270
                                   then
                                     let uu____8316 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8316 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8437  ->
                                                   fun uu____8438  ->
                                                     match (uu____8437,
                                                             uu____8438)
                                                     with
                                                     | ((x,uu____8464),
                                                        (b,uu____8466)) ->
                                                         let uu____8487 =
                                                           let uu____8494 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8494)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8487)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8502 =
                                            let uu____8531 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8531)  in
                                          (uu____8502, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8630 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8630 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8803) ->
                              let uu____8808 =
                                let uu____8837 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8837  in
                              (uu____8808, true)
                          | uu____8930 when Prims.op_Negation norm1 ->
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
                          | uu____8933 ->
                              let uu____8934 =
                                let uu____8936 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____8938 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____8936 uu____8938
                                 in
                              failwith uu____8934)
                     | uu____8974 ->
                         let rec aux' t_norm2 =
                           let uu____9014 =
                             let uu____9015 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____9015.FStar_Syntax_Syntax.n  in
                           match uu____9014 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____9073 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____9073 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____9116 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____9116 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____9243) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____9248 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___386_9320  ->
                  match () with
                  | () ->
                      let uu____9327 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9327
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9343 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9406  ->
                                   fun lb  ->
                                     match uu____9406 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9461 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9461
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9467 =
                                             let uu____9476 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9476
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9467 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9343 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9606 =
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
                               | uu____9619 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9629 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9629 vars)
                                   else
                                     (let uu____9632 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9632)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9693;
                                    FStar_Syntax_Syntax.lbeff = uu____9694;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9696;
                                    FStar_Syntax_Syntax.lbpos = uu____9697;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9721 =
                                     let uu____9730 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9730 with
                                     | (tcenv',uu____9748,e_t) ->
                                         let uu____9754 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9771 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____9754 with
                                          | (e1,t_norm1) ->
                                              ((let uu___387_9798 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___387_9798.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9721 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9812 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9812 with
                                         | ((binders,body,uu____9834,t_body),curry)
                                             ->
                                             ((let uu____9848 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9848
                                               then
                                                 let uu____9853 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9856 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9853 uu____9856
                                               else ());
                                              (let uu____9861 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9861 with
                                               | (vars,guards,env'1,binder_decls,uu____9888)
                                                   ->
                                                   let body1 =
                                                     let uu____9902 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9902
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
                                                     let uu____9926 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____9926 curry
                                                       fvb vars
                                                      in
                                                   let uu____9927 =
                                                     let is_logical =
                                                       let uu____9940 =
                                                         let uu____9941 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____9941.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____9940 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____9947 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____9951 =
                                                         let uu____9952 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____9952
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____9951
                                                         (fun lid  ->
                                                            let uu____9961 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____9961
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____9962 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____9962
                                                     then
                                                       let uu____9978 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____9979 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____9978,
                                                         uu____9979)
                                                     else
                                                       (let uu____9990 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____9990))
                                                      in
                                                   (match uu____9927 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____10014 =
                                                            let uu____10022 =
                                                              let uu____10023
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____10024
                                                                =
                                                                let uu____10035
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____10035)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____10023
                                                                uu____10024
                                                               in
                                                            let uu____10044 =
                                                              let uu____10045
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____10045
                                                               in
                                                            (uu____10022,
                                                              uu____10044,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____10014
                                                           in
                                                        let uu____10051 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____10051
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
                               | uu____10072 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10137 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____10137,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10143 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10196  ->
                                         fun fvb  ->
                                           match uu____10196 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10251 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10251
                                                  in
                                               let gtok =
                                                 let uu____10255 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10255
                                                  in
                                               let env4 =
                                                 let uu____10258 =
                                                   let uu____10261 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10261
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10258
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10143 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10388
                                     t_norm uu____10390 =
                                     match (uu____10388, uu____10390) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10422;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10423;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10425;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10426;_})
                                         ->
                                         let uu____10453 =
                                           let uu____10462 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10462 with
                                           | (tcenv',uu____10480,e_t) ->
                                               let uu____10486 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10503 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10486 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___388_10530 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___388_10530.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10453 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10549 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10549
                                                then
                                                  let uu____10554 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10556 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10558 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10554 uu____10556
                                                    uu____10558
                                                else ());
                                               (let uu____10563 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10563 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10603 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10603
                                                      then
                                                        let uu____10608 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10611 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10613 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10616 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10608
                                                          uu____10611
                                                          uu____10613
                                                          uu____10616
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10626 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10626 with
                                                      | (vars,guards,env'1,binder_decls,uu____10657)
                                                          ->
                                                          let decl_g =
                                                            let uu____10671 =
                                                              let uu____10683
                                                                =
                                                                let uu____10686
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10686
                                                                 in
                                                              (g,
                                                                uu____10683,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10671
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
                                                            let uu____10706 =
                                                              let uu____10714
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10714)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10706
                                                             in
                                                          let gsapp =
                                                            let uu____10721 =
                                                              let uu____10729
                                                                =
                                                                let uu____10732
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10732
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10729)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10721
                                                             in
                                                          let gmax =
                                                            let uu____10741 =
                                                              let uu____10749
                                                                =
                                                                let uu____10752
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____10752
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10749)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10741
                                                             in
                                                          let body1 =
                                                            let uu____10761 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____10761
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10766 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10766
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10784
                                                                   =
                                                                   let uu____10792
                                                                    =
                                                                    let uu____10793
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10794
                                                                    =
                                                                    let uu____10810
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
                                                                    uu____10810)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10793
                                                                    uu____10794
                                                                     in
                                                                   let uu____10824
                                                                    =
                                                                    let uu____10825
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10825
                                                                     in
                                                                   (uu____10792,
                                                                    uu____10824,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10784
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10832
                                                                   =
                                                                   let uu____10840
                                                                    =
                                                                    let uu____10841
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10842
                                                                    =
                                                                    let uu____10853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10853)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10841
                                                                    uu____10842
                                                                     in
                                                                   (uu____10840,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10832
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10867
                                                                   =
                                                                   let uu____10875
                                                                    =
                                                                    let uu____10876
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10877
                                                                    =
                                                                    let uu____10888
                                                                    =
                                                                    let uu____10889
                                                                    =
                                                                    let uu____10894
                                                                    =
                                                                    let uu____10895
                                                                    =
                                                                    let uu____10903
                                                                    =
                                                                    let uu____10906
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10906
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10903)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10895
                                                                     in
                                                                    (gsapp,
                                                                    uu____10894)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10889
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10888)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10876
                                                                    uu____10877
                                                                     in
                                                                   (uu____10875,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10867
                                                                  in
                                                               let uu____10923
                                                                 =
                                                                 let uu____10932
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____10932
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____10961)
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
                                                                    let uu____10983
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10983
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____10985
                                                                    =
                                                                    let uu____10993
                                                                    =
                                                                    let uu____10994
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10995
                                                                    =
                                                                    let uu____11006
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11006)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10994
                                                                    uu____10995
                                                                     in
                                                                    (uu____10993,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10985
                                                                     in
                                                                    let uu____11019
                                                                    =
                                                                    let uu____11028
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____11028
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____11043
                                                                    =
                                                                    let uu____11046
                                                                    =
                                                                    let uu____11047
                                                                    =
                                                                    let uu____11055
                                                                    =
                                                                    let uu____11056
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____11057
                                                                    =
                                                                    let uu____11068
                                                                    =
                                                                    let uu____11069
                                                                    =
                                                                    let uu____11074
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____11074,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11069
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____11068)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11056
                                                                    uu____11057
                                                                     in
                                                                    (uu____11055,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11047
                                                                     in
                                                                    [uu____11046]
                                                                     in
                                                                    (d3,
                                                                    uu____11043)
                                                                     in
                                                                    (match uu____11019
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
                                                               (match uu____10923
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
                                   let uu____11137 =
                                     let uu____11150 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11213  ->
                                          fun uu____11214  ->
                                            match (uu____11213, uu____11214)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11339 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11339 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11150
                                      in
                                   (match uu____11137 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11412 =
                                          let isDeclFun uu___371_11427 =
                                            match uu___371_11427 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11429 -> true
                                            | uu____11442 -> false  in
                                          let uu____11444 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11444
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11412 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11484 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___372_11490  ->
                                        match uu___372_11490 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11493 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11501 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11501)))
                                in
                             if uu____11484
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___390_11523  ->
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
                   let uu____11561 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11561
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
        let uu____11631 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11631 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11637 = encode_sigelt' env se  in
      match uu____11637 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11649 =
                  let uu____11650 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11650  in
                [uu____11649]
            | uu____11653 ->
                let uu____11654 =
                  let uu____11657 =
                    let uu____11658 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11658  in
                  uu____11657 :: g  in
                let uu____11661 =
                  let uu____11664 =
                    let uu____11665 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11665  in
                  [uu____11664]  in
                FStar_List.append uu____11654 uu____11661
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
        let uu____11681 =
          let uu____11682 = FStar_Syntax_Subst.compress t  in
          uu____11682.FStar_Syntax_Syntax.n  in
        match uu____11681 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11687)) -> s = "opaque_to_smt"
        | uu____11692 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11701 =
          let uu____11702 = FStar_Syntax_Subst.compress t  in
          uu____11702.FStar_Syntax_Syntax.n  in
        match uu____11701 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11707)) -> s = "uninterpreted_by_smt"
        | uu____11712 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11718 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11724 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____11736 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____11737 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11738 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11751 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11753 =
            let uu____11755 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____11755  in
          if uu____11753
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11784 ->
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
               let uu____11816 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11816 with
               | (formals,uu____11836) ->
                   let arity = FStar_List.length formals  in
                   let uu____11860 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11860 with
                    | (aname,atok,env2) ->
                        let uu____11886 =
                          let uu____11891 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11891 env2
                           in
                        (match uu____11886 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11903 =
                                 let uu____11904 =
                                   let uu____11916 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____11936  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11916,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11904
                                  in
                               [uu____11903;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____11953 =
                               let aux uu____12014 uu____12015 =
                                 match (uu____12014, uu____12015) with
                                 | ((bv,uu____12074),(env3,acc_sorts,acc)) ->
                                     let uu____12121 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____12121 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____11953 with
                              | (uu____12205,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____12231 =
                                      let uu____12239 =
                                        let uu____12240 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12241 =
                                          let uu____12252 =
                                            let uu____12253 =
                                              let uu____12258 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____12258)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12253
                                             in
                                          ([[app]], xs_sorts, uu____12252)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12240 uu____12241
                                         in
                                      (uu____12239,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12231
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
                                    let uu____12275 =
                                      let uu____12283 =
                                        let uu____12284 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12285 =
                                          let uu____12296 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12296)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12284 uu____12285
                                         in
                                      (uu____12283,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12275
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12311 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12311 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12337,uu____12338)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12339 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12339 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12361,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12368 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___373_12374  ->
                      match uu___373_12374 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12377 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12383 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12386 -> false))
               in
            Prims.op_Negation uu____12368  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12396 =
               let uu____12403 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12403 env fv t quals  in
             match uu____12396 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12422 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12422 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12442 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12442 with
           | (uvs,f1) ->
               let env1 =
                 let uu___391_12454 = env  in
                 let uu____12455 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___391_12454.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___391_12454.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___391_12454.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12455;
                   FStar_SMTEncoding_Env.warn =
                     (uu___391_12454.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___391_12454.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___391_12454.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___391_12454.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___391_12454.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___391_12454.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___391_12454.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12457 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12457 with
                | (f3,decls) ->
                    let g =
                      let uu____12471 =
                        let uu____12472 =
                          let uu____12480 =
                            let uu____12481 =
                              let uu____12483 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12483
                               in
                            FStar_Pervasives_Native.Some uu____12481  in
                          let uu____12487 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12480, uu____12487)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12472  in
                      [uu____12471]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12492) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12506 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12528 =
                       let uu____12531 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12531.FStar_Syntax_Syntax.fv_name  in
                     uu____12528.FStar_Syntax_Syntax.v  in
                   let uu____12532 =
                     let uu____12534 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12534  in
                   if uu____12532
                   then
                     let val_decl =
                       let uu___392_12566 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___392_12566.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___392_12566.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___392_12566.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12567 = encode_sigelt' env1 val_decl  in
                     match uu____12567 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12506 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12603,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12605;
                          FStar_Syntax_Syntax.lbtyp = uu____12606;
                          FStar_Syntax_Syntax.lbeff = uu____12607;
                          FStar_Syntax_Syntax.lbdef = uu____12608;
                          FStar_Syntax_Syntax.lbattrs = uu____12609;
                          FStar_Syntax_Syntax.lbpos = uu____12610;_}::[]),uu____12611)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12630 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12630 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12673 =
                   let uu____12676 =
                     let uu____12677 =
                       let uu____12685 =
                         let uu____12686 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12687 =
                           let uu____12698 =
                             let uu____12699 =
                               let uu____12704 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12704)  in
                             FStar_SMTEncoding_Util.mkEq uu____12699  in
                           ([[b2t_x]], [xx], uu____12698)  in
                         FStar_SMTEncoding_Term.mkForall uu____12686
                           uu____12687
                          in
                       (uu____12685,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12677  in
                   [uu____12676]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12673
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____12736,uu____12737) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___374_12747  ->
                  match uu___374_12747 with
                  | FStar_Syntax_Syntax.Discriminator uu____12749 -> true
                  | uu____12751 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____12753,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____12765 =
                     let uu____12767 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____12767.FStar_Ident.idText  in
                   uu____12765 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___375_12774  ->
                     match uu___375_12774 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12777 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12780) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___376_12794  ->
                  match uu___376_12794 with
                  | FStar_Syntax_Syntax.Projector uu____12796 -> true
                  | uu____12802 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12806 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12806 with
           | FStar_Pervasives_Native.Some uu____12813 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___393_12815 = se  in
                 let uu____12816 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12816;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___393_12815.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___393_12815.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___393_12815.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12819) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12834) ->
          let uu____12843 = encode_sigelts env ses  in
          (match uu____12843 with
           | (g,env1) ->
               let uu____12860 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___377_12883  ->
                         match uu___377_12883 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12885;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12886;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12887;_}
                             -> false
                         | uu____12894 -> true))
                  in
               (match uu____12860 with
                | (g',inversions) ->
                    let uu____12910 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___378_12931  ->
                              match uu___378_12931 with
                              | FStar_SMTEncoding_Term.DeclFun uu____12933 ->
                                  true
                              | uu____12946 -> false))
                       in
                    (match uu____12910 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12963,tps,k,uu____12966,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___379_12985  ->
                    match uu___379_12985 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12989 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13002 = c  in
              match uu____13002 with
              | (name,args,uu____13007,uu____13008,uu____13009) ->
                  let uu____13020 =
                    let uu____13021 =
                      let uu____13033 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13060  ->
                                match uu____13060 with
                                | (uu____13069,sort,uu____13071) -> sort))
                         in
                      (name, uu____13033, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13021  in
                  [uu____13020]
            else
              (let uu____13082 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____13082 c)
             in
          let inversion_axioms tapp vars =
            let uu____13110 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13118 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____13118 FStar_Option.isNone))
               in
            if uu____13110
            then []
            else
              (let uu____13153 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____13153 with
               | (xxsym,xx) ->
                   let uu____13166 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13205  ->
                             fun l  ->
                               match uu____13205 with
                               | (out,decls) ->
                                   let uu____13225 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____13225 with
                                    | (uu____13236,data_t) ->
                                        let uu____13238 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13238 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13282 =
                                                 let uu____13283 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13283.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13282 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13286,indices) ->
                                                   indices
                                               | uu____13312 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13342  ->
                                                         match uu____13342
                                                         with
                                                         | (x,uu____13350) ->
                                                             let uu____13355
                                                               =
                                                               let uu____13356
                                                                 =
                                                                 let uu____13364
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13364,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13356
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13355)
                                                    env)
                                                in
                                             let uu____13369 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13369 with
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
                                                      let uu____13399 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13417
                                                                 =
                                                                 let uu____13422
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13422,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13417)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13399
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13425 =
                                                      let uu____13426 =
                                                        let uu____13431 =
                                                          let uu____13432 =
                                                            let uu____13437 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13437,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13432
                                                           in
                                                        (out, uu____13431)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13426
                                                       in
                                                    (uu____13425,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13166 with
                    | (data_ax,decls) ->
                        let uu____13450 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13450 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13467 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13467 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13474 =
                                 let uu____13482 =
                                   let uu____13483 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13484 =
                                     let uu____13495 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13508 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13495,
                                       uu____13508)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13483 uu____13484
                                    in
                                 let uu____13517 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13482,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13517)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13474
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13523 =
            let uu____13528 =
              let uu____13529 = FStar_Syntax_Subst.compress k  in
              uu____13529.FStar_Syntax_Syntax.n  in
            match uu____13528 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13564 -> (tps, k)  in
          (match uu____13523 with
           | (formals,res) ->
               let uu____13571 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13571 with
                | (formals1,res1) ->
                    let uu____13582 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13582 with
                     | (vars,guards,env',binder_decls,uu____13607) ->
                         let arity = FStar_List.length vars  in
                         let uu____13621 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13621 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13651 =
                                  let uu____13659 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13659)  in
                                FStar_SMTEncoding_Util.mkApp uu____13651  in
                              let uu____13665 =
                                let tname_decl =
                                  let uu____13675 =
                                    let uu____13676 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13704  ->
                                              match uu____13704 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13725 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13676,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13725, false)
                                     in
                                  constructor_or_logic_type_decl uu____13675
                                   in
                                let uu____13733 =
                                  match vars with
                                  | [] ->
                                      let uu____13746 =
                                        let uu____13747 =
                                          let uu____13750 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____13750
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____13747
                                         in
                                      ([], uu____13746)
                                  | uu____13762 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13772 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13772
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13788 =
                                          let uu____13796 =
                                            let uu____13797 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13798 =
                                              let uu____13814 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13814)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13797 uu____13798
                                             in
                                          (uu____13796,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13788
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13733 with
                                | (tok_decls,env2) ->
                                    let uu____13841 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13841
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13665 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13869 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13869 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13891 =
                                               let uu____13892 =
                                                 let uu____13900 =
                                                   let uu____13901 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13901
                                                    in
                                                 (uu____13900,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13892
                                                in
                                             [uu____13891]
                                           else []  in
                                         let uu____13909 =
                                           let uu____13912 =
                                             let uu____13915 =
                                               let uu____13916 =
                                                 let uu____13924 =
                                                   let uu____13925 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____13926 =
                                                     let uu____13937 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13937)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____13925 uu____13926
                                                    in
                                                 (uu____13924,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13916
                                                in
                                             [uu____13915]  in
                                           FStar_List.append karr uu____13912
                                            in
                                         FStar_List.append decls1 uu____13909
                                      in
                                   let aux =
                                     let uu____13952 =
                                       let uu____13955 =
                                         inversion_axioms tapp vars  in
                                       let uu____13958 =
                                         let uu____13961 =
                                           let uu____13962 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____13962 env2
                                             tapp vars
                                            in
                                         [uu____13961]  in
                                       FStar_List.append uu____13955
                                         uu____13958
                                        in
                                     FStar_List.append kindingAx uu____13952
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13967,uu____13968,uu____13969,uu____13970,uu____13971)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13979,t,uu____13981,n_tps,uu____13983) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____13993 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____13993 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____14041 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____14041 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____14069 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____14069 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14089 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____14089 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14168 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____14168,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14175 =
                                  let uu____14176 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14176, true)
                                   in
                                let uu____14184 =
                                  let uu____14191 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____14191
                                   in
                                FStar_All.pipe_right uu____14175 uu____14184
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
                              let uu____14203 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____14203 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14215::uu____14216 ->
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
                                         let uu____14275 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____14276 =
                                           let uu____14287 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14287)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____14275 uu____14276
                                     | uu____14308 -> tok_typing  in
                                   let uu____14319 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14319 with
                                    | (vars',guards',env'',decls_formals,uu____14344)
                                        ->
                                        let uu____14357 =
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
                                        (match uu____14357 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14387 ->
                                                   let uu____14396 =
                                                     let uu____14397 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14397
                                                      in
                                                   [uu____14396]
                                                in
                                             let encode_elim uu____14413 =
                                               let uu____14414 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14414 with
                                               | (head1,args) ->
                                                   let uu____14465 =
                                                     let uu____14466 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14466.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14465 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14478;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14479;_},uu____14480)
                                                        ->
                                                        let uu____14485 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14485
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14506
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14506
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
                                                                    uu____14560
                                                                    ->
                                                                    let uu____14561
                                                                    =
                                                                    let uu____14567
                                                                    =
                                                                    let uu____14569
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14569
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14567)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14561
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14589
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14591
                                                                     in
                                                                    if
                                                                    uu____14589
                                                                    then
                                                                    let uu____14607
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14607]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14610
                                                                    =
                                                                    let uu____14624
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14681
                                                                     ->
                                                                    fun
                                                                    uu____14682
                                                                     ->
                                                                    match 
                                                                    (uu____14681,
                                                                    uu____14682)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14793
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14801
                                                                     in
                                                                    (match uu____14793
                                                                    with
                                                                    | 
                                                                    (uu____14815,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14826
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14826
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14831
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14831
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
                                                                    uu____14624
                                                                     in
                                                                  (match uu____14610
                                                                   with
                                                                   | 
                                                                   (uu____14852,arg_vars,elim_eqns_or_guards,uu____14855)
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
                                                                    let uu____14882
                                                                    =
                                                                    let uu____14890
                                                                    =
                                                                    let uu____14891
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14892
                                                                    =
                                                                    let uu____14903
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14905
                                                                    =
                                                                    let uu____14906
                                                                    =
                                                                    let uu____14911
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14911)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14906
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14903,
                                                                    uu____14905)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14891
                                                                    uu____14892
                                                                     in
                                                                    (uu____14890,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14882
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14926
                                                                    =
                                                                    let uu____14932
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14932,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14926
                                                                     in
                                                                    let uu____14935
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14935
                                                                    then
                                                                    let x =
                                                                    let uu____14944
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14944,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14949
                                                                    =
                                                                    let uu____14957
                                                                    =
                                                                    let uu____14958
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14959
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14975
                                                                    =
                                                                    let uu____14978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14978]
                                                                     in
                                                                    [uu____14975]
                                                                     in
                                                                    let uu____14983
                                                                    =
                                                                    let uu____14984
                                                                    =
                                                                    let uu____14989
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14991
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14989,
                                                                    uu____14991)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14984
                                                                     in
                                                                    (uu____14970,
                                                                    [x],
                                                                    uu____14983)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14958
                                                                    uu____14959
                                                                     in
                                                                    let uu____15006
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14957,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15006)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14949
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15017
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
                                                                    (let uu____15055
                                                                    =
                                                                    let uu____15056
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15056
                                                                    dapp1  in
                                                                    [uu____15055])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15017
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15071
                                                                    =
                                                                    let uu____15072
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15073
                                                                    =
                                                                    let uu____15084
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15086
                                                                    =
                                                                    let uu____15087
                                                                    =
                                                                    let uu____15092
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15092)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15087
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15084,
                                                                    uu____15086)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15072
                                                                    uu____15073
                                                                     in
                                                                    (uu____15071,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15063)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____15110 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____15110
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____15131
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____15131
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
                                                                    uu____15185
                                                                    ->
                                                                    let uu____15186
                                                                    =
                                                                    let uu____15192
                                                                    =
                                                                    let uu____15194
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15194
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15192)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15186
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15214
                                                                    =
                                                                    let uu____15216
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15216
                                                                     in
                                                                    if
                                                                    uu____15214
                                                                    then
                                                                    let uu____15232
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15232]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____15235
                                                                    =
                                                                    let uu____15249
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15306
                                                                     ->
                                                                    fun
                                                                    uu____15307
                                                                     ->
                                                                    match 
                                                                    (uu____15306,
                                                                    uu____15307)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15418
                                                                    =
                                                                    let uu____15426
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15426
                                                                     in
                                                                    (match uu____15418
                                                                    with
                                                                    | 
                                                                    (uu____15440,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15451
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15451
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15456
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15456
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
                                                                    uu____15249
                                                                     in
                                                                  (match uu____15235
                                                                   with
                                                                   | 
                                                                   (uu____15477,arg_vars,elim_eqns_or_guards,uu____15480)
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
                                                                    let uu____15507
                                                                    =
                                                                    let uu____15515
                                                                    =
                                                                    let uu____15516
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15517
                                                                    =
                                                                    let uu____15528
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15530
                                                                    =
                                                                    let uu____15531
                                                                    =
                                                                    let uu____15536
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15536)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15531
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15528,
                                                                    uu____15530)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15516
                                                                    uu____15517
                                                                     in
                                                                    (uu____15515,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15507
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15551
                                                                    =
                                                                    let uu____15557
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15557,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15551
                                                                     in
                                                                    let uu____15560
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15560
                                                                    then
                                                                    let x =
                                                                    let uu____15569
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15569,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15574
                                                                    =
                                                                    let uu____15582
                                                                    =
                                                                    let uu____15583
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15584
                                                                    =
                                                                    let uu____15595
                                                                    =
                                                                    let uu____15600
                                                                    =
                                                                    let uu____15603
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15603]
                                                                     in
                                                                    [uu____15600]
                                                                     in
                                                                    let uu____15608
                                                                    =
                                                                    let uu____15609
                                                                    =
                                                                    let uu____15614
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15616
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15614,
                                                                    uu____15616)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15609
                                                                     in
                                                                    (uu____15595,
                                                                    [x],
                                                                    uu____15608)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15583
                                                                    uu____15584
                                                                     in
                                                                    let uu____15631
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15582,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15631)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15574
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15642
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
                                                                    (let uu____15680
                                                                    =
                                                                    let uu____15681
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15681
                                                                    dapp1  in
                                                                    [uu____15680])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15642
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15688
                                                                    =
                                                                    let uu____15696
                                                                    =
                                                                    let uu____15697
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15698
                                                                    =
                                                                    let uu____15709
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15711
                                                                    =
                                                                    let uu____15712
                                                                    =
                                                                    let uu____15717
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15717)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15712
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15709,
                                                                    uu____15711)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15697
                                                                    uu____15698
                                                                     in
                                                                    (uu____15696,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15688)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15734 ->
                                                        ((let uu____15736 =
                                                            let uu____15742 =
                                                              let uu____15744
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____15746
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____15744
                                                                uu____15746
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____15742)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15736);
                                                         ([], [])))
                                                in
                                             let uu____15754 = encode_elim ()
                                                in
                                             (match uu____15754 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15780 =
                                                      let uu____15783 =
                                                        let uu____15786 =
                                                          let uu____15789 =
                                                            let uu____15792 =
                                                              let uu____15793
                                                                =
                                                                let uu____15805
                                                                  =
                                                                  let uu____15806
                                                                    =
                                                                    let uu____15808
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15808
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15806
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15805)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15793
                                                               in
                                                            [uu____15792]  in
                                                          let uu____15815 =
                                                            let uu____15818 =
                                                              let uu____15821
                                                                =
                                                                let uu____15824
                                                                  =
                                                                  let uu____15827
                                                                    =
                                                                    let uu____15830
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15835
                                                                    =
                                                                    let uu____15838
                                                                    =
                                                                    let uu____15839
                                                                    =
                                                                    let uu____15847
                                                                    =
                                                                    let uu____15848
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15849
                                                                    =
                                                                    let uu____15860
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15860)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15848
                                                                    uu____15849
                                                                     in
                                                                    (uu____15847,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15839
                                                                     in
                                                                    let uu____15873
                                                                    =
                                                                    let uu____15876
                                                                    =
                                                                    let uu____15877
                                                                    =
                                                                    let uu____15885
                                                                    =
                                                                    let uu____15886
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15887
                                                                    =
                                                                    let uu____15898
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15898,
                                                                    uu____15900)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15886
                                                                    uu____15887
                                                                     in
                                                                    (uu____15885,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15877
                                                                     in
                                                                    [uu____15876]
                                                                     in
                                                                    uu____15838
                                                                    ::
                                                                    uu____15873
                                                                     in
                                                                    uu____15830
                                                                    ::
                                                                    uu____15835
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15827
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15824
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15821
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15818
                                                             in
                                                          FStar_List.append
                                                            uu____15789
                                                            uu____15815
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15786
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15783
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15780
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
           (fun uu____15938  ->
              fun se  ->
                match uu____15938 with
                | (g,env1) ->
                    let uu____15958 = encode_sigelt env1 se  in
                    (match uu____15958 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16026 =
        match uu____16026 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____16063 ->
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
                 ((let uu____16071 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____16071
                   then
                     let uu____16076 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____16078 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____16080 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16076 uu____16078 uu____16080
                   else ());
                  (let uu____16085 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____16085 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____16103 =
                         let uu____16111 =
                           let uu____16113 =
                             let uu____16115 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16115
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16113  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16111
                          in
                       (match uu____16103 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16135 = FStar_Options.log_queries ()
                                 in
                              if uu____16135
                              then
                                let uu____16138 =
                                  let uu____16140 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16142 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16144 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16140 uu____16142 uu____16144
                                   in
                                FStar_Pervasives_Native.Some uu____16138
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16168,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16188 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16188 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16215 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16215 with | (uu____16242,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____16258 'Auu____16259 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____16258 *
      'Auu____16259) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16332  ->
              match uu____16332 with
              | (l,uu____16345,uu____16346) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16397  ->
              match uu____16397 with
              | (l,uu____16412,uu____16413) ->
                  let uu____16424 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16427 =
                    let uu____16430 =
                      let uu____16431 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16431  in
                    [uu____16430]  in
                  uu____16424 :: uu____16427))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16460 =
      let uu____16463 =
        let uu____16464 = FStar_Util.psmap_empty ()  in
        let uu____16479 = FStar_Util.psmap_empty ()  in
        let uu____16482 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16486 =
          let uu____16488 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16488 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16464;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16479;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16482;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16486;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16463]  in
    FStar_ST.op_Colon_Equals last_env uu____16460
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16530 = FStar_ST.op_Bang last_env  in
      match uu____16530 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16558 ->
          let uu___394_16561 = e  in
          let uu____16562 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___394_16561.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___394_16561.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___394_16561.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___394_16561.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___394_16561.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___394_16561.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___394_16561.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___394_16561.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16562;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___394_16561.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16570 = FStar_ST.op_Bang last_env  in
    match uu____16570 with
    | [] -> failwith "Empty env stack"
    | uu____16597::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16629  ->
    let uu____16630 = FStar_ST.op_Bang last_env  in
    match uu____16630 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16690  ->
    let uu____16691 = FStar_ST.op_Bang last_env  in
    match uu____16691 with
    | [] -> failwith "Popping an empty stack"
    | uu____16718::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16755  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16808  ->
         let uu____16809 = snapshot_env ()  in
         match uu____16809 with
         | (env_depth,()) ->
             let uu____16831 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16831 with
              | (varops_depth,()) ->
                  let uu____16853 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16853 with
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
        (fun uu____16911  ->
           let uu____16912 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16912 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____17007 = snapshot msg  in () 
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
        | (uu____17053::uu____17054,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___395_17062 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___395_17062.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___395_17062.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___395_17062.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17063 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____17083 =
        let uu____17086 =
          let uu____17087 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____17087  in
        let uu____17088 = open_fact_db_tags env  in uu____17086 ::
          uu____17088
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17083
  
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
      let uu____17115 = encode_sigelt env se  in
      match uu____17115 with
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
        let uu____17160 = FStar_Options.log_queries ()  in
        if uu____17160
        then
          let uu____17165 =
            let uu____17166 =
              let uu____17168 =
                let uu____17170 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17170 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17168  in
            FStar_SMTEncoding_Term.Caption uu____17166  in
          uu____17165 :: decls
        else decls  in
      (let uu____17189 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____17189
       then
         let uu____17192 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17192
       else ());
      (let env =
         let uu____17198 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17198 tcenv  in
       let uu____17199 = encode_top_level_facts env se  in
       match uu____17199 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17213 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17213)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17227 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17227
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17242 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____17242
          then
            let uu____17245 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17245
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17291  ->
                    fun se  ->
                      match uu____17291 with
                      | (g,env2) ->
                          let uu____17311 = encode_top_level_facts env2 se
                             in
                          (match uu____17311 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17334 =
            encode_signature
              (let uu___396_17343 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___396_17343.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___396_17343.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___396_17343.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___396_17343.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___396_17343.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___396_17343.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___396_17343.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___396_17343.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___396_17343.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___396_17343.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17334 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17363 = FStar_Options.log_queries ()  in
                if uu____17363
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
                 (let uu___397_17380 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___397_17380.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___397_17380.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___397_17380.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___397_17380.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___397_17380.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___397_17380.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___397_17380.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___397_17380.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___397_17380.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___397_17380.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17383 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17383
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
        (let uu____17448 =
           let uu____17450 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17450.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17448);
        (let env =
           let uu____17452 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17452 tcenv  in
         let uu____17453 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17492 = aux rest  in
                 (match uu____17492 with
                  | (out,rest1) ->
                      let t =
                        let uu____17520 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17520 with
                        | FStar_Pervasives_Native.Some uu____17523 ->
                            let uu____17524 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17524
                              x.FStar_Syntax_Syntax.sort
                        | uu____17525 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17529 =
                        let uu____17532 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___398_17535 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___398_17535.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___398_17535.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17532 :: out  in
                      (uu____17529, rest1))
             | uu____17540 -> ([], bindings)  in
           let uu____17547 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17547 with
           | (closing,bindings) ->
               let uu____17574 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17574, bindings)
            in
         match uu____17453 with
         | (q1,bindings) ->
             let uu____17605 = encode_env_bindings env bindings  in
             (match uu____17605 with
              | (env_decls,env1) ->
                  ((let uu____17627 =
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
                    if uu____17627
                    then
                      let uu____17634 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17634
                    else ());
                   (let uu____17639 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17639 with
                    | (phi,qdecls) ->
                        let uu____17660 =
                          let uu____17665 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17665 phi
                           in
                        (match uu____17660 with
                         | (labels,phi1) ->
                             let uu____17682 = encode_labels labels  in
                             (match uu____17682 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17719 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17719
                                    then
                                      let uu____17724 =
                                        let uu____17725 =
                                          let uu____17727 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17727
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17725
                                         in
                                      [uu____17724]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17736 =
                                      let uu____17744 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17745 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17744,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17745)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17736
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
  