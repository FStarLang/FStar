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
                let mk_binary_boolean_connective interp rng vname =
                  let macro_name =
                    Prims.strcat FStar_Ident.reserved_prefix vname  in
                  let i =
                    let uu____539 =
                      let uu____540 =
                        let uu____545 = FStar_SMTEncoding_Term.unboxBool x
                           in
                        let uu____546 = FStar_SMTEncoding_Term.unboxBool y
                           in
                        (uu____545, uu____546)  in
                      interp uu____540  in
                    FStar_SMTEncoding_Term.boxBool uu____539  in
                  let uu____547 =
                    let uu____560 = quant xy i  in uu____560 rng vname  in
                  match uu____547 with
                  | (uu____594,tok,arity,decls) ->
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
                let mk_op_and =
                  mk_binary_boolean_connective FStar_SMTEncoding_Util.mkAnd
                   in
                let mk_op_or =
                  mk_binary_boolean_connective FStar_SMTEncoding_Util.mkOr
                   in
                let prims1 =
                  let uu____691 =
                    let uu____715 =
                      let uu____737 =
                        let uu____738 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____738
                         in
                      quant axy uu____737  in
                    (FStar_Parser_Const.op_Eq, uu____715)  in
                  let uu____758 =
                    let uu____784 =
                      let uu____808 =
                        let uu____830 =
                          let uu____831 =
                            let uu____832 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____832  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____831
                           in
                        quant axy uu____830  in
                      (FStar_Parser_Const.op_notEq, uu____808)  in
                    let uu____852 =
                      let uu____878 =
                        let uu____902 =
                          let uu____924 =
                            let uu____925 =
                              let uu____926 =
                                let uu____931 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____932 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____931, uu____932)  in
                              FStar_SMTEncoding_Util.mkLT uu____926  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____925
                             in
                          quant xy uu____924  in
                        (FStar_Parser_Const.op_LT, uu____902)  in
                      let uu____952 =
                        let uu____978 =
                          let uu____1002 =
                            let uu____1024 =
                              let uu____1025 =
                                let uu____1026 =
                                  let uu____1031 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____1032 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____1031, uu____1032)  in
                                FStar_SMTEncoding_Util.mkLTE uu____1026  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1025
                               in
                            quant xy uu____1024  in
                          (FStar_Parser_Const.op_LTE, uu____1002)  in
                        let uu____1052 =
                          let uu____1078 =
                            let uu____1102 =
                              let uu____1124 =
                                let uu____1125 =
                                  let uu____1126 =
                                    let uu____1131 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____1132 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____1131, uu____1132)  in
                                  FStar_SMTEncoding_Util.mkGT uu____1126  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1125
                                 in
                              quant xy uu____1124  in
                            (FStar_Parser_Const.op_GT, uu____1102)  in
                          let uu____1152 =
                            let uu____1178 =
                              let uu____1202 =
                                let uu____1224 =
                                  let uu____1225 =
                                    let uu____1226 =
                                      let uu____1231 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____1232 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____1231, uu____1232)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____1226
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1225
                                   in
                                quant xy uu____1224  in
                              (FStar_Parser_Const.op_GTE, uu____1202)  in
                            let uu____1252 =
                              let uu____1278 =
                                let uu____1302 =
                                  let uu____1324 =
                                    let uu____1325 =
                                      let uu____1326 =
                                        let uu____1331 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____1332 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____1331, uu____1332)  in
                                      FStar_SMTEncoding_Util.mkSub uu____1326
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____1325
                                     in
                                  quant xy uu____1324  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____1302)
                                 in
                              let uu____1352 =
                                let uu____1378 =
                                  let uu____1402 =
                                    let uu____1424 =
                                      let uu____1425 =
                                        let uu____1426 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____1426
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____1425
                                       in
                                    quant qx uu____1424  in
                                  (FStar_Parser_Const.op_Minus, uu____1402)
                                   in
                                let uu____1446 =
                                  let uu____1472 =
                                    let uu____1496 =
                                      let uu____1518 =
                                        let uu____1519 =
                                          let uu____1520 =
                                            let uu____1525 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1526 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1525, uu____1526)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1520
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1519
                                         in
                                      quant xy uu____1518  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1496)
                                     in
                                  let uu____1546 =
                                    let uu____1572 =
                                      let uu____1596 =
                                        let uu____1618 =
                                          let uu____1619 =
                                            let uu____1620 =
                                              let uu____1625 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1626 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1625, uu____1626)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1620
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1619
                                           in
                                        quant xy uu____1618  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1596)
                                       in
                                    let uu____1646 =
                                      let uu____1672 =
                                        let uu____1696 =
                                          let uu____1718 =
                                            let uu____1719 =
                                              let uu____1720 =
                                                let uu____1725 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1726 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1725, uu____1726)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1720
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1719
                                             in
                                          quant xy uu____1718  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1696)
                                         in
                                      let uu____1746 =
                                        let uu____1772 =
                                          let uu____1796 =
                                            let uu____1818 =
                                              let uu____1819 =
                                                let uu____1820 =
                                                  let uu____1825 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1826 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1825, uu____1826)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1820
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1819
                                               in
                                            quant xy uu____1818  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1796)
                                           in
                                        let uu____1846 =
                                          let uu____1872 =
                                            let uu____1898 =
                                              let uu____1924 =
                                                let uu____1948 =
                                                  let uu____1970 =
                                                    let uu____1971 =
                                                      let uu____1972 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1972
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1971
                                                     in
                                                  quant qx uu____1970  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1948)
                                                 in
                                              [uu____1924]  in
                                            (FStar_Parser_Const.op_Or,
                                              mk_op_or) :: uu____1898
                                             in
                                          (FStar_Parser_Const.op_And,
                                            mk_op_and) :: uu____1872
                                           in
                                        uu____1772 :: uu____1846  in
                                      uu____1672 :: uu____1746  in
                                    uu____1572 :: uu____1646  in
                                  uu____1472 :: uu____1546  in
                                uu____1378 :: uu____1446  in
                              uu____1278 :: uu____1352  in
                            uu____1178 :: uu____1252  in
                          uu____1078 :: uu____1152  in
                        uu____978 :: uu____1052  in
                      uu____878 :: uu____952  in
                    uu____784 :: uu____852  in
                  uu____691 :: uu____758  in
                let mk1 l v1 =
                  let uu____2423 =
                    let uu____2438 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____2540  ->
                              match uu____2540 with
                              | (l',uu____2564) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____2438
                      (FStar_Option.map
                         (fun uu____2681  ->
                            match uu____2681 with
                            | (uu____2715,b) ->
                                let uu____2755 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2755 v1))
                     in
                  FStar_All.pipe_right uu____2423 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2853  ->
                          match uu____2853 with
                          | (l',uu____2877) -> FStar_Ident.lid_equals l l'))
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
          let uu____2951 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2951 with
          | (xxsym,xx) ->
              let uu____2962 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2962 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2978 =
                     let uu____2986 =
                       let uu____2987 =
                         let uu____2998 =
                           let uu____2999 =
                             let uu____3004 =
                               let uu____3005 =
                                 let uu____3010 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____3010)  in
                               FStar_SMTEncoding_Util.mkEq uu____3005  in
                             (xx_has_type, uu____3004)  in
                           FStar_SMTEncoding_Util.mkImp uu____2999  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2998)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2987  in
                     let uu____3035 =
                       let uu____3037 =
                         let uu____3039 =
                           let uu____3041 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____3041  in
                         Prims.strcat module_name uu____3039  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3037
                        in
                     (uu____2986, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3035)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2978)
  
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
    let uu____3133 = f env.FStar_SMTEncoding_Env.tcenv s t  in
    (uu____3133, env)  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____3153 =
      let uu____3154 =
        let uu____3162 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____3162, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3154  in
    let uu____3167 =
      let uu____3170 =
        let uu____3171 =
          let uu____3179 =
            let uu____3180 =
              let uu____3191 =
                let uu____3192 =
                  let uu____3197 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____3197)  in
                FStar_SMTEncoding_Util.mkImp uu____3192  in
              ([[typing_pred]], [xx], uu____3191)  in
            let uu____3216 =
              let uu____3231 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3231  in
            uu____3216 uu____3180  in
          (uu____3179, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3171  in
      [uu____3170]  in
    uu____3153 :: uu____3167  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3264 =
      let uu____3265 =
        let uu____3273 =
          let uu____3274 = FStar_TypeChecker_Env.get_range env  in
          let uu____3275 =
            let uu____3286 =
              let uu____3291 =
                let uu____3294 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____3294]  in
              [uu____3291]  in
            let uu____3299 =
              let uu____3300 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3300 tt  in
            (uu____3286, [bb], uu____3299)  in
          FStar_SMTEncoding_Term.mkForall uu____3274 uu____3275  in
        (uu____3273, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3265  in
    let uu____3319 =
      let uu____3322 =
        let uu____3323 =
          let uu____3331 =
            let uu____3332 =
              let uu____3343 =
                let uu____3344 =
                  let uu____3349 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____3349)  in
                FStar_SMTEncoding_Util.mkImp uu____3344  in
              ([[typing_pred]], [xx], uu____3343)  in
            let uu____3370 =
              let uu____3385 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3385  in
            uu____3370 uu____3332  in
          (uu____3331, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3323  in
      [uu____3322]  in
    uu____3264 :: uu____3319  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____3409 =
        let uu____3415 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____3415, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____3409  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____3439 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3439  in
    let uu____3444 =
      let uu____3445 =
        let uu____3453 =
          let uu____3454 = FStar_TypeChecker_Env.get_range env  in
          let uu____3455 =
            let uu____3466 =
              let uu____3471 =
                let uu____3474 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____3474]  in
              [uu____3471]  in
            let uu____3479 =
              let uu____3480 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3480 tt  in
            (uu____3466, [bb], uu____3479)  in
          FStar_SMTEncoding_Term.mkForall uu____3454 uu____3455  in
        (uu____3453, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3445  in
    let uu____3499 =
      let uu____3502 =
        let uu____3503 =
          let uu____3511 =
            let uu____3512 =
              let uu____3523 =
                let uu____3524 =
                  let uu____3529 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____3529)  in
                FStar_SMTEncoding_Util.mkImp uu____3524  in
              ([[typing_pred]], [xx], uu____3523)  in
            let uu____3550 =
              let uu____3565 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3565  in
            uu____3550 uu____3512  in
          (uu____3511, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3503  in
      let uu____3570 =
        let uu____3573 =
          let uu____3574 =
            let uu____3582 =
              let uu____3583 =
                let uu____3594 =
                  let uu____3595 =
                    let uu____3600 =
                      let uu____3601 =
                        let uu____3604 =
                          let uu____3607 =
                            let uu____3610 =
                              let uu____3611 =
                                let uu____3616 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____3617 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____3616, uu____3617)  in
                              FStar_SMTEncoding_Util.mkGT uu____3611  in
                            let uu____3619 =
                              let uu____3622 =
                                let uu____3623 =
                                  let uu____3628 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____3629 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____3628, uu____3629)  in
                                FStar_SMTEncoding_Util.mkGTE uu____3623  in
                              let uu____3631 =
                                let uu____3634 =
                                  let uu____3635 =
                                    let uu____3640 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____3641 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____3640, uu____3641)  in
                                  FStar_SMTEncoding_Util.mkLT uu____3635  in
                                [uu____3634]  in
                              uu____3622 :: uu____3631  in
                            uu____3610 :: uu____3619  in
                          typing_pred_y :: uu____3607  in
                        typing_pred :: uu____3604  in
                      FStar_SMTEncoding_Util.mk_and_l uu____3601  in
                    (uu____3600, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____3595  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____3594)
                 in
              let uu____3665 =
                let uu____3680 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3680  in
              uu____3665 uu____3583  in
            (uu____3582,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____3574  in
        [uu____3573]  in
      uu____3502 :: uu____3570  in
    uu____3444 :: uu____3499  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____3713 =
      let uu____3714 =
        let uu____3722 =
          let uu____3723 = FStar_TypeChecker_Env.get_range env  in
          let uu____3724 =
            let uu____3735 =
              let uu____3740 =
                let uu____3743 = FStar_SMTEncoding_Term.boxString b  in
                [uu____3743]  in
              [uu____3740]  in
            let uu____3748 =
              let uu____3749 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____3749 tt  in
            (uu____3735, [bb], uu____3748)  in
          FStar_SMTEncoding_Term.mkForall uu____3723 uu____3724  in
        (uu____3722, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3714  in
    let uu____3768 =
      let uu____3771 =
        let uu____3772 =
          let uu____3780 =
            let uu____3781 =
              let uu____3792 =
                let uu____3793 =
                  let uu____3798 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____3798)  in
                FStar_SMTEncoding_Util.mkImp uu____3793  in
              ([[typing_pred]], [xx], uu____3792)  in
            let uu____3819 =
              let uu____3834 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3834  in
            uu____3819 uu____3781  in
          (uu____3780, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____3772  in
      [uu____3771]  in
    uu____3713 :: uu____3768  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    let uu____3862 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp")
       in
    [uu____3862]  in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3890 =
      let uu____3891 =
        let uu____3899 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3899, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3891  in
    [uu____3890]  in
  let mk_macro_name s = Prims.strcat FStar_Ident.reserved_prefix s  in
  let mk_binary_prop_connective conn interp env vname uu____3950 =
    let mkValid t = FStar_SMTEncoding_Util.mkApp ("Valid", [t])  in
    let squash env1 t =
      let sq =
        FStar_SMTEncoding_Env.lookup_lid env1 FStar_Parser_Const.squash_lid
         in
      let b2t1 =
        FStar_SMTEncoding_Env.lookup_lid env1 FStar_Parser_Const.b2t_lid  in
      let uu____3985 =
        let uu____3993 =
          let uu____3996 =
            let uu____3997 =
              let uu____4005 =
                let uu____4008 = FStar_SMTEncoding_Term.boxBool t  in
                [uu____4008]  in
              ((b2t1.FStar_SMTEncoding_Env.smt_id), uu____4005)  in
            FStar_SMTEncoding_Util.mkApp uu____3997  in
          [uu____3996]  in
        ((sq.FStar_SMTEncoding_Env.smt_id), uu____3993)  in
      FStar_SMTEncoding_Util.mkApp uu____3985  in
    let bind_macro env1 lid macro_name =
      let fvb = FStar_SMTEncoding_Env.lookup_lid env1 lid  in
      FStar_SMTEncoding_Env.push_free_var env1 lid
        fvb.FStar_SMTEncoding_Env.smt_arity macro_name
        fvb.FStar_SMTEncoding_Env.smt_token
       in
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
      let uu____4062 =
        let uu____4081 =
          let uu____4082 = interp (valid_a, valid_b)  in
          squash env uu____4082  in
        (macro_name, [aa; bb], FStar_SMTEncoding_Term.Term_sort, uu____4081,
          (FStar_Pervasives_Native.Some "macro for embedded connective"))
         in
      FStar_SMTEncoding_Term.mkDefineFun uu____4062  in
    let uu____4108 =
      let uu____4109 =
        let uu____4110 =
          let uu____4118 =
            let uu____4119 =
              FStar_TypeChecker_Env.get_range env.FStar_SMTEncoding_Env.tcenv
               in
            let uu____4120 =
              let uu____4131 =
                let uu____4132 =
                  let uu____4137 = interp (valid_a, valid_b)  in
                  (uu____4137, valid_conn_a_b)  in
                FStar_SMTEncoding_Util.mkIff uu____4132  in
              ([[conn_a_b]], [aa; bb], uu____4131)  in
            FStar_SMTEncoding_Term.mkForall uu____4119 uu____4120  in
          (uu____4118,
            (FStar_Pervasives_Native.Some
               (Prims.strcat vname " interpretation")),
            (Prims.strcat vname "-interp"))
           in
        FStar_SMTEncoding_Util.mkAssume uu____4110  in
      [uu____4109; macro]  in
    let uu____4165 = bind_macro env conn macro_name  in
    (uu____4108, uu____4165)  in
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
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____4275 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4275  in
    let uu____4280 =
      let uu____4281 =
        let uu____4289 =
          let uu____4290 = FStar_TypeChecker_Env.get_range env  in
          let uu____4291 =
            let uu____4302 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____4302)  in
          FStar_SMTEncoding_Term.mkForall uu____4290 uu____4291  in
        (uu____4289, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4281  in
    [uu____4280]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____4379 =
      let uu____4380 =
        let uu____4388 =
          let uu____4389 = FStar_TypeChecker_Env.get_range env  in
          let uu____4390 =
            let uu____4401 =
              let uu____4402 =
                let uu____4407 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4407, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4402  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____4401)  in
          FStar_SMTEncoding_Term.mkForall uu____4389 uu____4390  in
        (uu____4388, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4380  in
    [uu____4379]  in
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
    let uu____4503 =
      let uu____4504 =
        let uu____4512 =
          let uu____4513 = FStar_TypeChecker_Env.get_range env  in
          let uu____4514 =
            let uu____4525 =
              let uu____4526 =
                let uu____4531 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____4531, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____4526  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____4525)  in
          FStar_SMTEncoding_Term.mkForall uu____4513 uu____4514  in
        (uu____4512, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4504  in
    [uu____4503]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____4591 =
      let uu____4592 =
        let uu____4600 =
          let uu____4601 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____4601 range_ty  in
        let uu____4602 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____4600, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____4602)
         in
      FStar_SMTEncoding_Util.mkAssume uu____4592  in
    [uu____4591]  in
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
        let uu____4656 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4656 x1 t  in
      let uu____4658 = FStar_TypeChecker_Env.get_range env  in
      let uu____4659 =
        let uu____4670 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____4670)  in
      FStar_SMTEncoding_Term.mkForall uu____4658 uu____4659  in
    let uu____4689 =
      let uu____4690 =
        let uu____4698 =
          let uu____4699 = FStar_TypeChecker_Env.get_range env  in
          let uu____4700 =
            let uu____4711 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____4711)  in
          FStar_SMTEncoding_Term.mkForall uu____4699 uu____4700  in
        (uu____4698,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4690  in
    [uu____4689]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____4774 =
      let uu____4775 =
        let uu____4783 =
          let uu____4784 = FStar_TypeChecker_Env.get_range env  in
          let uu____4785 =
            let uu____4801 =
              let uu____4802 =
                let uu____4807 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____4808 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____4807, uu____4808)  in
              FStar_SMTEncoding_Util.mkAnd uu____4802  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____4801)
             in
          FStar_SMTEncoding_Term.mkForall' uu____4784 uu____4785  in
        (uu____4783,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4775  in
    [uu____4774]  in
  let mk_squash_interp env sq uu____4857 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_sq_a =
      let uu____4874 =
        let uu____4882 =
          let uu____4885 = FStar_SMTEncoding_Util.mkApp (sq, [a])  in
          [uu____4885]  in
        ("Valid", uu____4882)  in
      FStar_SMTEncoding_Util.mkApp uu____4874  in
    let uu____4893 =
      let uu____4894 =
        let uu____4902 =
          let uu____4903 = FStar_TypeChecker_Env.get_range env  in
          let uu____4904 =
            let uu____4915 =
              FStar_SMTEncoding_Util.mkIff (valid_sq_a, valid_a)  in
            ([[valid_sq_a]], [aa], uu____4915)  in
          FStar_SMTEncoding_Term.mkForall uu____4903 uu____4904  in
        (uu____4902,
          (FStar_Pervasives_Native.Some "valid-squash interpretation"),
          "valid-squash-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____4894  in
    [uu____4893]  in
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
    (FStar_Parser_Const.not_lid, (wrap mk_not_interp));
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
          let uu____5598 =
            FStar_Util.find_opt
              (fun uu____5644  ->
                 match uu____5644 with
                 | (l,uu____5664) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____5598 with
          | FStar_Pervasives_Native.None  -> ([], env)
          | FStar_Pervasives_Native.Some (uu____5725,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____5798 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____5798 with
        | (form,decls) ->
            let uu____5807 =
              let uu____5810 =
                FStar_SMTEncoding_Util.mkAssume
                  (form,
                    (FStar_Pervasives_Native.Some
                       (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                    (Prims.strcat "lemma_" lid.FStar_Ident.str))
                 in
              [uu____5810]  in
            FStar_List.append decls uu____5807
  
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
              let uu____5867 =
                ((let uu____5871 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____5871) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____5867
              then
                let arg_sorts =
                  let uu____5885 =
                    let uu____5886 = FStar_Syntax_Subst.compress t_norm  in
                    uu____5886.FStar_Syntax_Syntax.n  in
                  match uu____5885 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5892) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____5930  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____5937 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____5939 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____5939 with
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
                (let uu____5981 = prims.is lid  in
                 if uu____5981
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____5992 = prims.mk lid vname  in
                   match uu____5992 with
                   | (vname1,tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname1 (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____6032 =
                      let uu____6051 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____6051 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____6079 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____6079
                            then
                              let uu____6084 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___380_6087 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___380_6087.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___380_6087.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___380_6087.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___380_6087.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___380_6087.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___380_6087.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___380_6087.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___380_6087.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___380_6087.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___380_6087.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___380_6087.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___380_6087.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___380_6087.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___380_6087.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___380_6087.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___380_6087.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___380_6087.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___380_6087.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___380_6087.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___380_6087.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___380_6087.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___380_6087.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___380_6087.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___380_6087.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___380_6087.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___380_6087.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___380_6087.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___380_6087.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___380_6087.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___380_6087.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___380_6087.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___380_6087.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___380_6087.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___380_6087.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___380_6087.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___380_6087.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___380_6087.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___380_6087.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___380_6087.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___380_6087.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___380_6087.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___380_6087.FStar_TypeChecker_Env.nbe)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____6084
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____6110 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____6110)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____6032 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____6191 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____6191 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____6225 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___370_6286  ->
                                       match uu___370_6286 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____6290 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6290 with
                                            | (uu____6314,(xxsym,uu____6316))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____6340 =
                                                  let uu____6341 =
                                                    let uu____6349 =
                                                      let uu____6350 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6351 =
                                                        let uu____6362 =
                                                          let uu____6363 =
                                                            let uu____6368 =
                                                              let uu____6369
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____6369
                                                               in
                                                            (vapp,
                                                              uu____6368)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____6363
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6362)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6350 uu____6351
                                                       in
                                                    (uu____6349,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6341
                                                   in
                                                [uu____6340])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____6384 =
                                             FStar_Util.prefix vars  in
                                           (match uu____6384 with
                                            | (uu____6408,(xxsym,uu____6410))
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
                                                let uu____6442 =
                                                  let uu____6443 =
                                                    let uu____6451 =
                                                      let uu____6452 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____6453 =
                                                        let uu____6464 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____6464)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____6452 uu____6453
                                                       in
                                                    (uu____6451,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6443
                                                   in
                                                [uu____6442])
                                       | uu____6477 -> []))
                                in
                             let uu____6478 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____6478 with
                              | (vars,guards,env',decls1,uu____6505) ->
                                  let uu____6518 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____6531 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____6531, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____6535 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____6535 with
                                         | (g,ds) ->
                                             let uu____6548 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____6548,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____6518 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____6565 =
                                           let uu____6573 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____6573)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____6565
                                          in
                                       let uu____6579 =
                                         let vname_decl =
                                           let uu____6587 =
                                             let uu____6599 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____6619  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____6599,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____6587
                                            in
                                         let uu____6630 =
                                           let env2 =
                                             let uu___381_6636 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___381_6636.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____6637 =
                                             let uu____6639 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____6639  in
                                           if uu____6637
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____6630 with
                                         | (tok_typing,decls2) ->
                                             let uu____6656 =
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
                                                   let uu____6680 =
                                                     let uu____6681 =
                                                       let uu____6684 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_1  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_1)
                                                         uu____6684
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____6681
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____6680)
                                               | uu____6694 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____6709 =
                                                       let uu____6717 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____6717]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____6709
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____6739 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____6740 =
                                                       let uu____6751 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____6751)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____6739 uu____6740
                                                      in
                                                   let name_tok_corr =
                                                     let uu____6761 =
                                                       let uu____6769 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____6769,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____6761
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
                                                       let uu____6808 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6809 =
                                                         let uu____6820 =
                                                           let uu____6821 =
                                                             let uu____6826 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____6827 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____6826,
                                                               uu____6827)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____6821
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____6820)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6808
                                                         uu____6809
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
                                             (match uu____6656 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____6579 with
                                        | (decls2,env2) ->
                                            let uu____6878 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____6888 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____6888 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____6903 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____6903,
                                                    decls)
                                               in
                                            (match uu____6878 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____6920 =
                                                     let uu____6928 =
                                                       let uu____6929 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6930 =
                                                         let uu____6941 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____6941)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____6929
                                                         uu____6930
                                                        in
                                                     (uu____6928,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____6920
                                                    in
                                                 let freshness =
                                                   let uu____6957 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____6957
                                                   then
                                                     let uu____6965 =
                                                       let uu____6966 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____6967 =
                                                         let uu____6980 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____6998 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____6980,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____6998)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____6966
                                                         uu____6967
                                                        in
                                                     let uu____7004 =
                                                       let uu____7007 =
                                                         let uu____7008 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____7008 env2
                                                           vapp vars
                                                          in
                                                       [uu____7007]  in
                                                     uu____6965 :: uu____7004
                                                   else []  in
                                                 let g =
                                                   let uu____7014 =
                                                     let uu____7017 =
                                                       let uu____7020 =
                                                         let uu____7023 =
                                                           let uu____7026 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____7026
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____7023
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____7020
                                                        in
                                                     FStar_List.append decls2
                                                       uu____7017
                                                      in
                                                   FStar_List.append decls11
                                                     uu____7014
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
          let uu____7068 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____7068 with
          | FStar_Pervasives_Native.None  ->
              let uu____7079 = encode_free_var false env x t t_norm []  in
              (match uu____7079 with
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
            let uu____7150 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____7150 with
            | (decls,env1) ->
                let uu____7169 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____7169
                then
                  let uu____7178 =
                    let uu____7181 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____7181  in
                  (uu____7178, env1)
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
             (fun uu____7241  ->
                fun lb  ->
                  match uu____7241 with
                  | (decls,env1) ->
                      let uu____7261 =
                        let uu____7268 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____7268
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____7261 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____7301 = FStar_Syntax_Util.head_and_args t  in
    match uu____7301 with
    | (hd1,args) ->
        let uu____7345 =
          let uu____7346 = FStar_Syntax_Util.un_uinst hd1  in
          uu____7346.FStar_Syntax_Syntax.n  in
        (match uu____7345 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7352,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____7376 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____7387 -> false
  
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en  ->
    let uu___382_7395 = en  in
    let uu____7396 = FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache  in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___382_7395.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___382_7395.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___382_7395.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___382_7395.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___382_7395.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.cache = uu____7396;
      FStar_SMTEncoding_Env.nolabels =
        (uu___382_7395.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___382_7395.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___382_7395.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___382_7395.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___382_7395.FStar_SMTEncoding_Env.encoding_quantifier)
    }
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun uu____7428  ->
      fun quals  ->
        match uu____7428 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____7535 = FStar_Util.first_N nbinders formals  in
              match uu____7535 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____7636  ->
                         fun uu____7637  ->
                           match (uu____7636, uu____7637) with
                           | ((formal,uu____7663),(binder,uu____7665)) ->
                               let uu____7686 =
                                 let uu____7693 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____7693)  in
                               FStar_Syntax_Syntax.NT uu____7686) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____7707 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____7748  ->
                              match uu____7748 with
                              | (x,i) ->
                                  let uu____7767 =
                                    let uu___383_7768 = x  in
                                    let uu____7769 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_7768.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_7768.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7769
                                    }  in
                                  (uu____7767, i)))
                       in
                    FStar_All.pipe_right uu____7707
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____7793 =
                      let uu____7798 = FStar_Syntax_Subst.compress body  in
                      let uu____7799 =
                        let uu____7800 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____7800
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____7798 uu____7799
                       in
                    uu____7793 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____7885 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____7885
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___384_7892 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___384_7892.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___384_7892.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___384_7892.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___384_7892.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___384_7892.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___384_7892.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___384_7892.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___384_7892.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___384_7892.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___384_7892.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___384_7892.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___384_7892.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___384_7892.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___384_7892.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___384_7892.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___384_7892.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___384_7892.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___384_7892.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___384_7892.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___384_7892.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___384_7892.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___384_7892.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___384_7892.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___384_7892.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___384_7892.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___384_7892.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___384_7892.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___384_7892.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___384_7892.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___384_7892.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___384_7892.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___384_7892.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___384_7892.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___384_7892.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___384_7892.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___384_7892.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___384_7892.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___384_7892.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___384_7892.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___384_7892.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___384_7892.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___384_7892.FStar_TypeChecker_Env.nbe)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____7942 = FStar_Syntax_Util.abs_formals e  in
                match uu____7942 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8024::uu____8025 ->
                         let uu____8046 =
                           let uu____8047 =
                             let uu____8050 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____8050
                              in
                           uu____8047.FStar_Syntax_Syntax.n  in
                         (match uu____8046 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8108 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8108 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____8165 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____8165
                                   then
                                     let uu____8211 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8211 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____8332  ->
                                                   fun uu____8333  ->
                                                     match (uu____8332,
                                                             uu____8333)
                                                     with
                                                     | ((x,uu____8359),
                                                        (b,uu____8361)) ->
                                                         let uu____8382 =
                                                           let uu____8389 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____8389)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____8382)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____8397 =
                                            let uu____8426 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____8426)  in
                                          (uu____8397, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8525 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____8525 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8698) ->
                              let uu____8703 =
                                let uu____8732 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____8732  in
                              (uu____8703, true)
                          | uu____8825 when Prims.op_Negation norm1 ->
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
                          | uu____8828 ->
                              let uu____8829 =
                                let uu____8831 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____8833 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____8831 uu____8833
                                 in
                              failwith uu____8829)
                     | uu____8869 ->
                         let rec aux' t_norm2 =
                           let uu____8909 =
                             let uu____8910 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____8910.FStar_Syntax_Syntax.n  in
                           match uu____8909 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____8968 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____8968 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____9011 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____9011 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____9138) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____9143 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               (fun uu___386_9215  ->
                  match () with
                  | () ->
                      let uu____9222 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb  ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                         in
                      if uu____9222
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9238 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9301  ->
                                   fun lb  ->
                                     match uu____9301 with
                                     | (toks,typs,decls,env1) ->
                                         ((let uu____9356 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           if uu____9356
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             FStar_SMTEncoding_EncodeTerm.whnf
                                               env1
                                               lb.FStar_Syntax_Syntax.lbtyp
                                              in
                                           let uu____9362 =
                                             let uu____9371 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             declare_top_level_let env1
                                               uu____9371
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm
                                              in
                                           match uu____9362 with
                                           | (tok,decl,env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env))
                            in
                         match uu____9238 with
                         | (toks,typs,decls,env1) ->
                             let toks_fvbs = FStar_List.rev toks  in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten
                                in
                             let env_decls = copy_env env1  in
                             let typs1 = FStar_List.rev typs  in
                             let mk_app1 rng curry fvb vars =
                               let mk_fv uu____9501 =
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
                               | uu____9514 ->
                                   if curry
                                   then
                                     (match fvb.FStar_SMTEncoding_Env.smt_token
                                      with
                                      | FStar_Pervasives_Native.Some ftok ->
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            ftok vars
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____9524 = mk_fv ()  in
                                          FStar_SMTEncoding_EncodeTerm.mk_Apply
                                            uu____9524 vars)
                                   else
                                     (let uu____9527 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                        rng
                                        (FStar_SMTEncoding_Term.Var
                                           (fvb.FStar_SMTEncoding_Env.smt_id))
                                        fvb.FStar_SMTEncoding_Env.smt_arity
                                        uu____9527)
                                in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9588;
                                    FStar_Syntax_Syntax.lbeff = uu____9589;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9591;
                                    FStar_Syntax_Syntax.lbpos = uu____9592;_}::[],t_norm::[],fvb::[])
                                   ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid  in
                                   let uu____9616 =
                                     let uu____9625 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm]
                                        in
                                     match uu____9625 with
                                     | (tcenv',uu____9643,e_t) ->
                                         let uu____9649 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9666 ->
                                               failwith "Impossible"
                                            in
                                         (match uu____9649 with
                                          | (e1,t_norm1) ->
                                              ((let uu___387_9693 = env2  in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.cache
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.cache);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___387_9693.FStar_SMTEncoding_Env.encoding_quantifier)
                                                }), e1, t_norm1))
                                      in
                                   (match uu____9616 with
                                    | (env',e1,t_norm1) ->
                                        let uu____9707 =
                                          destruct_bound_function flid
                                            t_norm1 e1
                                           in
                                        (match uu____9707 with
                                         | ((binders,body,uu____9729,t_body),curry)
                                             ->
                                             ((let uu____9743 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____9743
                                               then
                                                 let uu____9748 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____9751 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9748 uu____9751
                                               else ());
                                              (let uu____9756 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____9756 with
                                               | (vars,guards,env'1,binder_decls,uu____9783)
                                                   ->
                                                   let body1 =
                                                     let uu____9797 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____9797
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
                                                     let uu____9821 =
                                                       FStar_Syntax_Util.range_of_lbname
                                                         lbn
                                                        in
                                                     mk_app1 uu____9821 curry
                                                       fvb vars
                                                      in
                                                   let uu____9822 =
                                                     let is_logical =
                                                       let uu____9835 =
                                                         let uu____9836 =
                                                           FStar_Syntax_Subst.compress
                                                             t_body
                                                            in
                                                         uu____9836.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____9835 with
                                                       | FStar_Syntax_Syntax.Tm_fvar
                                                           fv when
                                                           FStar_Syntax_Syntax.fv_eq_lid
                                                             fv
                                                             FStar_Parser_Const.logical_lid
                                                           -> true
                                                       | uu____9842 -> false
                                                        in
                                                     let is_prims =
                                                       let uu____9846 =
                                                         let uu____9847 =
                                                           FStar_All.pipe_right
                                                             lbn
                                                             FStar_Util.right
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____9847
                                                           FStar_Syntax_Syntax.lid_of_fv
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____9846
                                                         (fun lid  ->
                                                            let uu____9856 =
                                                              FStar_Ident.lid_of_ids
                                                                lid.FStar_Ident.ns
                                                               in
                                                            FStar_Ident.lid_equals
                                                              uu____9856
                                                              FStar_Parser_Const.prims_lid)
                                                        in
                                                     let uu____9857 =
                                                       (Prims.op_Negation
                                                          is_prims)
                                                         &&
                                                         ((FStar_All.pipe_right
                                                             quals
                                                             (FStar_List.contains
                                                                FStar_Syntax_Syntax.Logic))
                                                            || is_logical)
                                                        in
                                                     if uu____9857
                                                     then
                                                       let uu____9873 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let uu____9874 =
                                                         FStar_SMTEncoding_EncodeTerm.encode_formula
                                                           body1 env'1
                                                          in
                                                       (app, uu____9873,
                                                         uu____9874)
                                                     else
                                                       (let uu____9885 =
                                                          FStar_SMTEncoding_EncodeTerm.encode_term
                                                            body1 env'1
                                                           in
                                                        (app, app,
                                                          uu____9885))
                                                      in
                                                   (match uu____9822 with
                                                    | (pat,app1,(body2,decls2))
                                                        ->
                                                        let eqn =
                                                          let uu____9909 =
                                                            let uu____9917 =
                                                              let uu____9918
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____9919
                                                                =
                                                                let uu____9930
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body2)
                                                                   in
                                                                ([[pat]],
                                                                  vars,
                                                                  uu____9930)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____9918
                                                                uu____9919
                                                               in
                                                            let uu____9939 =
                                                              let uu____9940
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____9940
                                                               in
                                                            (uu____9917,
                                                              uu____9939,
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 fvb.FStar_SMTEncoding_Env.smt_id))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____9909
                                                           in
                                                        let uu____9946 =
                                                          primitive_type_axioms
                                                            env2 flid
                                                            fvb.FStar_SMTEncoding_Env.smt_id
                                                            app1
                                                           in
                                                        (match uu____9946
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
                               | uu____9967 -> failwith "Impossible"  in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____10032 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                     "fuel"
                                    in
                                 (uu____10032,
                                   FStar_SMTEncoding_Term.Fuel_sort)
                                  in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel  in
                               let env0 = env2  in
                               let uu____10038 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____10091  ->
                                         fun fvb  ->
                                           match uu____10091 with
                                           | (gtoks,env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid
                                                  in
                                               let g =
                                                 let uu____10146 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10146
                                                  in
                                               let gtok =
                                                 let uu____10150 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token"
                                                    in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____10150
                                                  in
                                               let env4 =
                                                 let uu____10153 =
                                                   let uu____10156 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm])
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_2  ->
                                                        FStar_Pervasives_Native.Some
                                                          _0_2) uu____10156
                                                    in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____10153
                                                  in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2))
                                  in
                               match uu____10038 with
                               | (gtoks,env3) ->
                                   let gtoks1 = FStar_List.rev gtoks  in
                                   let encode_one_binding env01 uu____10283
                                     t_norm uu____10285 =
                                     match (uu____10283, uu____10285) with
                                     | ((fvb,g,gtok),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbn;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = uu____10317;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____10318;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = e;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____10320;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____10321;_})
                                         ->
                                         let uu____10348 =
                                           let uu____10357 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm]
                                              in
                                           match uu____10357 with
                                           | (tcenv',uu____10375,e_t) ->
                                               let uu____10381 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10398 ->
                                                     failwith "Impossible"
                                                  in
                                               (match uu____10381 with
                                                | (e1,t_norm1) ->
                                                    ((let uu___388_10425 =
                                                        env3  in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.cache
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.cache);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___388_10425.FStar_SMTEncoding_Env.encoding_quantifier)
                                                      }), e1, t_norm1))
                                            in
                                         (match uu____10348 with
                                          | (env',e1,t_norm1) ->
                                              ((let uu____10444 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding")
                                                   in
                                                if uu____10444
                                                then
                                                  let uu____10449 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn
                                                     in
                                                  let uu____10451 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1
                                                     in
                                                  let uu____10453 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1
                                                     in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10449 uu____10451
                                                    uu____10453
                                                else ());
                                               (let uu____10458 =
                                                  destruct_bound_function
                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                    t_norm1 e1
                                                   in
                                                match uu____10458 with
                                                | ((binders,body,formals,tres),curry)
                                                    ->
                                                    ((let uu____10498 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env01.FStar_SMTEncoding_Env.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      if uu____10498
                                                      then
                                                        let uu____10503 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " binders
                                                           in
                                                        let uu____10506 =
                                                          FStar_Syntax_Print.term_to_string
                                                            body
                                                           in
                                                        let uu____10508 =
                                                          FStar_Syntax_Print.binders_to_string
                                                            ", " formals
                                                           in
                                                        let uu____10511 =
                                                          FStar_Syntax_Print.term_to_string
                                                            tres
                                                           in
                                                        FStar_Util.print4
                                                          "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                          uu____10503
                                                          uu____10506
                                                          uu____10508
                                                          uu____10511
                                                      else ());
                                                     if curry
                                                     then
                                                       failwith
                                                         "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     else ();
                                                     (let uu____10521 =
                                                        FStar_SMTEncoding_EncodeTerm.encode_binders
                                                          FStar_Pervasives_Native.None
                                                          binders env'
                                                         in
                                                      match uu____10521 with
                                                      | (vars,guards,env'1,binder_decls,uu____10552)
                                                          ->
                                                          let decl_g =
                                                            let uu____10566 =
                                                              let uu____10578
                                                                =
                                                                let uu____10581
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  ::
                                                                  uu____10581
                                                                 in
                                                              (g,
                                                                uu____10578,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (FStar_Pervasives_Native.Some
                                                                   "Fuel-instrumented function name"))
                                                               in
                                                            FStar_SMTEncoding_Term.DeclFun
                                                              uu____10566
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
                                                            let uu____10601 =
                                                              let uu____10609
                                                                =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                                uu____10609)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10601
                                                             in
                                                          let gsapp =
                                                            let uu____10616 =
                                                              let uu____10624
                                                                =
                                                                let uu____10627
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                uu____10627
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10624)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10616
                                                             in
                                                          let gmax =
                                                            let uu____10636 =
                                                              let uu____10644
                                                                =
                                                                let uu____10647
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                uu____10647
                                                                  :: vars_tm
                                                                 in
                                                              (g,
                                                                uu____10644)
                                                               in
                                                            FStar_SMTEncoding_Util.mkApp
                                                              uu____10636
                                                             in
                                                          let body1 =
                                                            let uu____10656 =
                                                              FStar_TypeChecker_Env.is_reifiable_function
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                t_norm1
                                                               in
                                                            if uu____10656
                                                            then
                                                              FStar_TypeChecker_Util.reify_body
                                                                env'1.FStar_SMTEncoding_Env.tcenv
                                                                body
                                                            else body  in
                                                          let uu____10661 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_term
                                                              body1 env'1
                                                             in
                                                          (match uu____10661
                                                           with
                                                           | (body_tm,decls2)
                                                               ->
                                                               let eqn_g =
                                                                 let uu____10679
                                                                   =
                                                                   let uu____10687
                                                                    =
                                                                    let uu____10688
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10689
                                                                    =
                                                                    let uu____10705
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
                                                                    uu____10705)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10688
                                                                    uu____10689
                                                                     in
                                                                   let uu____10719
                                                                    =
                                                                    let uu____10720
                                                                    =
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10720
                                                                     in
                                                                   (uu____10687,
                                                                    uu____10719,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10679
                                                                  in
                                                               let eqn_f =
                                                                 let uu____10727
                                                                   =
                                                                   let uu____10735
                                                                    =
                                                                    let uu____10736
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10737
                                                                    =
                                                                    let uu____10748
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10748)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10736
                                                                    uu____10737
                                                                     in
                                                                   (uu____10735,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10727
                                                                  in
                                                               let eqn_g' =
                                                                 let uu____10762
                                                                   =
                                                                   let uu____10770
                                                                    =
                                                                    let uu____10771
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10772
                                                                    =
                                                                    let uu____10783
                                                                    =
                                                                    let uu____10784
                                                                    =
                                                                    let uu____10789
                                                                    =
                                                                    let uu____10790
                                                                    =
                                                                    let uu____10798
                                                                    =
                                                                    let uu____10801
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____10801
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____10798)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____10790
                                                                     in
                                                                    (gsapp,
                                                                    uu____10789)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10784
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10783)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10771
                                                                    uu____10772
                                                                     in
                                                                   (uu____10770,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkAssume
                                                                   uu____10762
                                                                  in
                                                               let uu____10818
                                                                 =
                                                                 let uu____10827
                                                                   =
                                                                   FStar_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    formals
                                                                    env02
                                                                    in
                                                                 match uu____10827
                                                                 with
                                                                 | (vars1,v_guards,env4,binder_decls1,uu____10856)
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
                                                                    let uu____10878
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10878
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                    let uu____10880
                                                                    =
                                                                    let uu____10888
                                                                    =
                                                                    let uu____10889
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10890
                                                                    =
                                                                    let uu____10901
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10901)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10889
                                                                    uu____10890
                                                                     in
                                                                    (uu____10888,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10880
                                                                     in
                                                                    let uu____10914
                                                                    =
                                                                    let uu____10923
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp  in
                                                                    match uu____10923
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____10938
                                                                    =
                                                                    let uu____10941
                                                                    =
                                                                    let uu____10942
                                                                    =
                                                                    let uu____10950
                                                                    =
                                                                    let uu____10951
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____10952
                                                                    =
                                                                    let uu____10963
                                                                    =
                                                                    let uu____10964
                                                                    =
                                                                    let uu____10969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____10969,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____10964
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____10963)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10951
                                                                    uu____10952
                                                                     in
                                                                    (uu____10950,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10942
                                                                     in
                                                                    [uu____10941]
                                                                     in
                                                                    (d3,
                                                                    uu____10938)
                                                                     in
                                                                    (match uu____10914
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
                                                               (match uu____10818
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
                                   let uu____11032 =
                                     let uu____11045 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1
                                        in
                                     FStar_List.fold_left
                                       (fun uu____11108  ->
                                          fun uu____11109  ->
                                            match (uu____11108, uu____11109)
                                            with
                                            | ((decls2,eqns,env01),(gtok,ty,lb))
                                                ->
                                                let uu____11234 =
                                                  encode_one_binding env01
                                                    gtok ty lb
                                                   in
                                                (match uu____11234 with
                                                 | (decls',eqns',env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____11045
                                      in
                                   (match uu____11032 with
                                    | (decls2,eqns,env01) ->
                                        let uu____11307 =
                                          let isDeclFun uu___371_11322 =
                                            match uu___371_11322 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____11324 -> true
                                            | uu____11337 -> false  in
                                          let uu____11339 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten
                                             in
                                          FStar_All.pipe_right uu____11339
                                            (FStar_List.partition isDeclFun)
                                           in
                                        (match uu____11307 with
                                         | (prefix_decls,rest) ->
                                             let eqns1 = FStar_List.rev eqns
                                                in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append rest
                                                    eqns1)), env01)))
                                in
                             let uu____11379 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___372_11385  ->
                                        match uu___372_11385 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                             -> true
                                        | uu____11388 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t  ->
                                          let uu____11396 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_TypeChecker_Env.is_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t)
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11396)))
                                in
                             if uu____11379
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___390_11418  ->
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
                   let uu____11456 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____11456
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
        let uu____11526 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____11526 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____11532 = encode_sigelt' env se  in
      match uu____11532 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____11544 =
                  let uu____11545 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____11545  in
                [uu____11544]
            | uu____11548 ->
                let uu____11549 =
                  let uu____11552 =
                    let uu____11553 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11553  in
                  uu____11552 :: g  in
                let uu____11556 =
                  let uu____11559 =
                    let uu____11560 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____11560  in
                  [uu____11559]  in
                FStar_List.append uu____11549 uu____11556
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
        let uu____11576 =
          let uu____11577 = FStar_Syntax_Subst.compress t  in
          uu____11577.FStar_Syntax_Syntax.n  in
        match uu____11576 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11582)) -> s = "opaque_to_smt"
        | uu____11587 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____11596 =
          let uu____11597 = FStar_Syntax_Subst.compress t  in
          uu____11597.FStar_Syntax_Syntax.n  in
        match uu____11596 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____11602)) -> s = "uninterpreted_by_smt"
        | uu____11607 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11613 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____11619 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____11631 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____11632 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11633 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____11646 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____11648 =
            let uu____11650 =
              FStar_TypeChecker_Env.is_reifiable_effect
                env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname
               in
            Prims.op_Negation uu____11650  in
          if uu____11648
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____11679 ->
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
               let uu____11711 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____11711 with
               | (formals,uu____11731) ->
                   let arity = FStar_List.length formals  in
                   let uu____11755 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____11755 with
                    | (aname,atok,env2) ->
                        let uu____11781 =
                          let uu____11786 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term
                            uu____11786 env2
                           in
                        (match uu____11781 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____11798 =
                                 let uu____11799 =
                                   let uu____11811 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____11831  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____11811,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____11799
                                  in
                               [uu____11798;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____11848 =
                               let aux uu____11909 uu____11910 =
                                 match (uu____11909, uu____11910) with
                                 | ((bv,uu____11969),(env3,acc_sorts,acc)) ->
                                     let uu____12016 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____12016 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____11848 with
                              | (uu____12100,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____12126 =
                                      let uu____12134 =
                                        let uu____12135 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12136 =
                                          let uu____12147 =
                                            let uu____12148 =
                                              let uu____12153 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____12153)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12148
                                             in
                                          ([[app]], xs_sorts, uu____12147)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12135 uu____12136
                                         in
                                      (uu____12134,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12126
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
                                    let uu____12170 =
                                      let uu____12178 =
                                        let uu____12179 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____12180 =
                                          let uu____12191 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12191)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____12179 uu____12180
                                         in
                                      (uu____12178,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12170
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12206 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12206 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12232,uu____12233)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____12234 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____12234 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12256,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____12263 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___373_12269  ->
                      match uu___373_12269 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____12272 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____12278 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12281 -> false))
               in
            Prims.op_Negation uu____12263  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____12291 =
               let uu____12298 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____12298 env fv t quals  in
             match uu____12291 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12317 = primitive_type_axioms env1 lid tname tsym
                    in
                 (match uu____12317 with
                  | (pt_axioms,env2) ->
                      ((FStar_List.append decls pt_axioms), env2)))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____12337 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____12337 with
           | (uvs,f1) ->
               let env1 =
                 let uu___391_12349 = env  in
                 let uu____12350 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___391_12349.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___391_12349.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___391_12349.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____12350;
                   FStar_SMTEncoding_Env.warn =
                     (uu___391_12349.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___391_12349.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___391_12349.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___391_12349.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___391_12349.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___391_12349.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___391_12349.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____12352 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____12352 with
                | (f3,decls) ->
                    let g =
                      let uu____12366 =
                        let uu____12367 =
                          let uu____12375 =
                            let uu____12376 =
                              let uu____12378 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____12378
                               in
                            FStar_Pervasives_Native.Some uu____12376  in
                          let uu____12382 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____12375, uu____12382)  in
                        FStar_SMTEncoding_Util.mkAssume uu____12367  in
                      [uu____12366]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____12387) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____12401 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12423 =
                       let uu____12426 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12426.FStar_Syntax_Syntax.fv_name  in
                     uu____12423.FStar_Syntax_Syntax.v  in
                   let uu____12427 =
                     let uu____12429 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12429  in
                   if uu____12427
                   then
                     let val_decl =
                       let uu___392_12461 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___392_12461.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___392_12461.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___392_12461.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____12462 = encode_sigelt' env1 val_decl  in
                     match uu____12462 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____12401 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12498,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12500;
                          FStar_Syntax_Syntax.lbtyp = uu____12501;
                          FStar_Syntax_Syntax.lbeff = uu____12502;
                          FStar_Syntax_Syntax.lbdef = uu____12503;
                          FStar_Syntax_Syntax.lbattrs = uu____12504;
                          FStar_Syntax_Syntax.lbpos = uu____12505;_}::[]),uu____12506)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____12525 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____12525 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____12568 =
                   let uu____12571 =
                     let uu____12572 =
                       let uu____12580 =
                         let uu____12581 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____12582 =
                           let uu____12593 =
                             let uu____12594 =
                               let uu____12599 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____12599)  in
                             FStar_SMTEncoding_Util.mkEq uu____12594  in
                           ([[b2t_x]], [xx], uu____12593)  in
                         FStar_SMTEncoding_Term.mkForall uu____12581
                           uu____12582
                          in
                       (uu____12580,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____12572  in
                   [uu____12571]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____12568
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____12631,uu____12632) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___374_12642  ->
                  match uu___374_12642 with
                  | FStar_Syntax_Syntax.Discriminator uu____12644 -> true
                  | uu____12646 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____12648,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____12660 =
                     let uu____12662 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____12662.FStar_Ident.idText  in
                   uu____12660 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___375_12669  ->
                     match uu___375_12669 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____12672 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____12675) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___376_12689  ->
                  match uu___376_12689 with
                  | FStar_Syntax_Syntax.Projector uu____12691 -> true
                  | uu____12697 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____12701 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____12701 with
           | FStar_Pervasives_Native.Some uu____12708 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___393_12710 = se  in
                 let uu____12711 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____12711;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___393_12710.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___393_12710.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___393_12710.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____12714) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____12729) ->
          let uu____12738 = encode_sigelts env ses  in
          (match uu____12738 with
           | (g,env1) ->
               let uu____12755 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___377_12778  ->
                         match uu___377_12778 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____12780;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____12781;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____12782;_}
                             -> false
                         | uu____12789 -> true))
                  in
               (match uu____12755 with
                | (g',inversions) ->
                    let uu____12805 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___378_12826  ->
                              match uu___378_12826 with
                              | FStar_SMTEncoding_Term.DeclFun uu____12828 ->
                                  true
                              | uu____12841 -> false))
                       in
                    (match uu____12805 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____12858,tps,k,uu____12861,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___379_12880  ->
                    match uu___379_12880 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____12884 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____12897 = c  in
              match uu____12897 with
              | (name,args,uu____12902,uu____12903,uu____12904) ->
                  let uu____12915 =
                    let uu____12916 =
                      let uu____12928 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____12955  ->
                                match uu____12955 with
                                | (uu____12964,sort,uu____12966) -> sort))
                         in
                      (name, uu____12928, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____12916  in
                  [uu____12915]
            else
              (let uu____12977 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____12977 c)
             in
          let inversion_axioms tapp vars =
            let uu____13005 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13013 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____13013 FStar_Option.isNone))
               in
            if uu____13005
            then []
            else
              (let uu____13048 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____13048 with
               | (xxsym,xx) ->
                   let uu____13061 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13100  ->
                             fun l  ->
                               match uu____13100 with
                               | (out,decls) ->
                                   let uu____13120 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____13120 with
                                    | (uu____13131,data_t) ->
                                        let uu____13133 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13133 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13177 =
                                                 let uu____13178 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13178.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13177 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13181,indices) ->
                                                   indices
                                               | uu____13207 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13237  ->
                                                         match uu____13237
                                                         with
                                                         | (x,uu____13245) ->
                                                             let uu____13250
                                                               =
                                                               let uu____13251
                                                                 =
                                                                 let uu____13259
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13259,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13251
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____13250)
                                                    env)
                                                in
                                             let uu____13264 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____13264 with
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
                                                      let uu____13294 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13312
                                                                 =
                                                                 let uu____13317
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13317,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13312)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13294
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13320 =
                                                      let uu____13321 =
                                                        let uu____13326 =
                                                          let uu____13327 =
                                                            let uu____13332 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13332,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13327
                                                           in
                                                        (out, uu____13326)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13321
                                                       in
                                                    (uu____13320,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13061 with
                    | (data_ax,decls) ->
                        let uu____13345 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____13345 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13362 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13362 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13369 =
                                 let uu____13377 =
                                   let uu____13378 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____13379 =
                                     let uu____13390 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13403 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13390,
                                       uu____13403)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____13378 uu____13379
                                    in
                                 let uu____13412 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13377,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13412)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____13369
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____13418 =
            let uu____13423 =
              let uu____13424 = FStar_Syntax_Subst.compress k  in
              uu____13424.FStar_Syntax_Syntax.n  in
            match uu____13423 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13459 -> (tps, k)  in
          (match uu____13418 with
           | (formals,res) ->
               let uu____13466 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13466 with
                | (formals1,res1) ->
                    let uu____13477 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____13477 with
                     | (vars,guards,env',binder_decls,uu____13502) ->
                         let arity = FStar_List.length vars  in
                         let uu____13516 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____13516 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13546 =
                                  let uu____13554 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13554)  in
                                FStar_SMTEncoding_Util.mkApp uu____13546  in
                              let uu____13560 =
                                let tname_decl =
                                  let uu____13570 =
                                    let uu____13571 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13599  ->
                                              match uu____13599 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13620 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____13571,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13620, false)
                                     in
                                  constructor_or_logic_type_decl uu____13570
                                   in
                                let uu____13628 =
                                  match vars with
                                  | [] ->
                                      let uu____13641 =
                                        let uu____13642 =
                                          let uu____13645 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_3  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_3) uu____13645
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____13642
                                         in
                                      ([], uu____13641)
                                  | uu____13657 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13667 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13667
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13683 =
                                          let uu____13691 =
                                            let uu____13692 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____13693 =
                                              let uu____13709 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____13709)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____13692 uu____13693
                                             in
                                          (uu____13691,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13683
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13628 with
                                | (tok_decls,env2) ->
                                    let uu____13736 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____13736
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____13560 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13764 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____13764 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13786 =
                                               let uu____13787 =
                                                 let uu____13795 =
                                                   let uu____13796 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13796
                                                    in
                                                 (uu____13795,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13787
                                                in
                                             [uu____13786]
                                           else []  in
                                         let uu____13804 =
                                           let uu____13807 =
                                             let uu____13810 =
                                               let uu____13811 =
                                                 let uu____13819 =
                                                   let uu____13820 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____13821 =
                                                     let uu____13832 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13832)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____13820 uu____13821
                                                    in
                                                 (uu____13819,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13811
                                                in
                                             [uu____13810]  in
                                           FStar_List.append karr uu____13807
                                            in
                                         FStar_List.append decls1 uu____13804
                                      in
                                   let aux =
                                     let uu____13847 =
                                       let uu____13850 =
                                         inversion_axioms tapp vars  in
                                       let uu____13853 =
                                         let uu____13856 =
                                           let uu____13857 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____13857 env2
                                             tapp vars
                                            in
                                         [uu____13856]  in
                                       FStar_List.append uu____13850
                                         uu____13853
                                        in
                                     FStar_List.append kindingAx uu____13847
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13862,uu____13863,uu____13864,uu____13865,uu____13866)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13874,t,uu____13876,n_tps,uu____13878) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____13888 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____13888 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____13936 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____13936 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____13964 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____13964 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13984 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____13984 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14063 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____14063,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14070 =
                                  let uu____14071 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14071, true)
                                   in
                                let uu____14079 =
                                  let uu____14086 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____14086
                                   in
                                FStar_All.pipe_right uu____14070 uu____14079
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
                              let uu____14098 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____14098 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14110::uu____14111 ->
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
                                         let uu____14170 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____14171 =
                                           let uu____14182 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14182)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____14170 uu____14171
                                     | uu____14203 -> tok_typing  in
                                   let uu____14214 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____14214 with
                                    | (vars',guards',env'',decls_formals,uu____14239)
                                        ->
                                        let uu____14252 =
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
                                        (match uu____14252 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14282 ->
                                                   let uu____14291 =
                                                     let uu____14292 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14292
                                                      in
                                                   [uu____14291]
                                                in
                                             let encode_elim uu____14308 =
                                               let uu____14309 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14309 with
                                               | (head1,args) ->
                                                   let uu____14360 =
                                                     let uu____14361 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14361.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14360 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14373;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14374;_},uu____14375)
                                                        ->
                                                        let uu____14380 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____14380
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____14401
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____14401
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
                                                                    uu____14455
                                                                    ->
                                                                    let uu____14456
                                                                    =
                                                                    let uu____14462
                                                                    =
                                                                    let uu____14464
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14464
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14462)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____14456
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14484
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14486
                                                                     in
                                                                    if
                                                                    uu____14484
                                                                    then
                                                                    let uu____14502
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14502]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____14505
                                                                    =
                                                                    let uu____14519
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____14576
                                                                     ->
                                                                    fun
                                                                    uu____14577
                                                                     ->
                                                                    match 
                                                                    (uu____14576,
                                                                    uu____14577)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____14688
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14696
                                                                     in
                                                                    (match uu____14688
                                                                    with
                                                                    | 
                                                                    (uu____14710,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14721
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____14721
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14726
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14726
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
                                                                    uu____14519
                                                                     in
                                                                  (match uu____14505
                                                                   with
                                                                   | 
                                                                   (uu____14747,arg_vars,elim_eqns_or_guards,uu____14750)
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
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14798
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14800
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14806)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14801
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14798,
                                                                    uu____14800)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14786
                                                                    uu____14787
                                                                     in
                                                                    (uu____14785,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14777
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____14821
                                                                    =
                                                                    let uu____14827
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____14827,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14821
                                                                     in
                                                                    let uu____14830
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____14830
                                                                    then
                                                                    let x =
                                                                    let uu____14839
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____14839,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14844
                                                                    =
                                                                    let uu____14852
                                                                    =
                                                                    let uu____14853
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14854
                                                                    =
                                                                    let uu____14865
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14873]
                                                                     in
                                                                    [uu____14870]
                                                                     in
                                                                    let uu____14878
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14884
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14886
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14884,
                                                                    uu____14886)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14879
                                                                     in
                                                                    (uu____14865,
                                                                    [x],
                                                                    uu____14878)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14853
                                                                    uu____14854
                                                                     in
                                                                    let uu____14901
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14852,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14901)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14844
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14912
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
                                                                    (let uu____14950
                                                                    =
                                                                    let uu____14951
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____14951
                                                                    dapp1  in
                                                                    [uu____14950])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14912
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14958
                                                                    =
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14967
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____14968
                                                                    =
                                                                    let uu____14979
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14981
                                                                    =
                                                                    let uu____14982
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14987)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14982
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14979,
                                                                    uu____14981)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14967
                                                                    uu____14968
                                                                     in
                                                                    (uu____14966,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14958)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____15005 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____15005
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____15026
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____15026
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
                                                                    uu____15080
                                                                    ->
                                                                    let uu____15081
                                                                    =
                                                                    let uu____15087
                                                                    =
                                                                    let uu____15089
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15089
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____15087)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____15081
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15109
                                                                    =
                                                                    let uu____15111
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15111
                                                                     in
                                                                    if
                                                                    uu____15109
                                                                    then
                                                                    let uu____15127
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15127]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____15130
                                                                    =
                                                                    let uu____15144
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____15201
                                                                     ->
                                                                    fun
                                                                    uu____15202
                                                                     ->
                                                                    match 
                                                                    (uu____15201,
                                                                    uu____15202)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15313
                                                                    =
                                                                    let uu____15321
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____15321
                                                                     in
                                                                    (match uu____15313
                                                                    with
                                                                    | 
                                                                    (uu____15335,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15346
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____15346
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15351
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15351
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
                                                                    uu____15144
                                                                     in
                                                                  (match uu____15130
                                                                   with
                                                                   | 
                                                                   (uu____15372,arg_vars,elim_eqns_or_guards,uu____15375)
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
                                                                    let uu____15402
                                                                    =
                                                                    let uu____15410
                                                                    =
                                                                    let uu____15411
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15412
                                                                    =
                                                                    let uu____15423
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15425
                                                                    =
                                                                    let uu____15426
                                                                    =
                                                                    let uu____15431
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15431)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15426
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15423,
                                                                    uu____15425)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15411
                                                                    uu____15412
                                                                     in
                                                                    (uu____15410,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15402
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____15446
                                                                    =
                                                                    let uu____15452
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____15452,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15446
                                                                     in
                                                                    let uu____15455
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____15455
                                                                    then
                                                                    let x =
                                                                    let uu____15464
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____15464,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15469
                                                                    =
                                                                    let uu____15477
                                                                    =
                                                                    let uu____15478
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15479
                                                                    =
                                                                    let uu____15490
                                                                    =
                                                                    let uu____15495
                                                                    =
                                                                    let uu____15498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15498]
                                                                     in
                                                                    [uu____15495]
                                                                     in
                                                                    let uu____15503
                                                                    =
                                                                    let uu____15504
                                                                    =
                                                                    let uu____15509
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15511
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15509,
                                                                    uu____15511)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15504
                                                                     in
                                                                    (uu____15490,
                                                                    [x],
                                                                    uu____15503)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15478
                                                                    uu____15479
                                                                     in
                                                                    let uu____15526
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15477,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15526)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15469
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15537
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
                                                                    (let uu____15575
                                                                    =
                                                                    let uu____15576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____15576
                                                                    dapp1  in
                                                                    [uu____15575])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15537
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15583
                                                                    =
                                                                    let uu____15591
                                                                    =
                                                                    let uu____15592
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15593
                                                                    =
                                                                    let uu____15604
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15606
                                                                    =
                                                                    let uu____15607
                                                                    =
                                                                    let uu____15612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15612)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15607
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15604,
                                                                    uu____15606)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15592
                                                                    uu____15593
                                                                     in
                                                                    (uu____15591,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15583)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____15629 ->
                                                        ((let uu____15631 =
                                                            let uu____15637 =
                                                              let uu____15639
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____15641
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____15639
                                                                uu____15641
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____15637)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15631);
                                                         ([], [])))
                                                in
                                             let uu____15649 = encode_elim ()
                                                in
                                             (match uu____15649 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15675 =
                                                      let uu____15678 =
                                                        let uu____15681 =
                                                          let uu____15684 =
                                                            let uu____15687 =
                                                              let uu____15688
                                                                =
                                                                let uu____15700
                                                                  =
                                                                  let uu____15701
                                                                    =
                                                                    let uu____15703
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15703
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15701
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15700)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15688
                                                               in
                                                            [uu____15687]  in
                                                          let uu____15710 =
                                                            let uu____15713 =
                                                              let uu____15716
                                                                =
                                                                let uu____15719
                                                                  =
                                                                  let uu____15722
                                                                    =
                                                                    let uu____15725
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))
                                                                     in
                                                                    let uu____15730
                                                                    =
                                                                    let uu____15733
                                                                    =
                                                                    let uu____15734
                                                                    =
                                                                    let uu____15742
                                                                    =
                                                                    let uu____15743
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15744
                                                                    =
                                                                    let uu____15755
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15755)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15743
                                                                    uu____15744
                                                                     in
                                                                    (uu____15742,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15734
                                                                     in
                                                                    let uu____15768
                                                                    =
                                                                    let uu____15771
                                                                    =
                                                                    let uu____15772
                                                                    =
                                                                    let uu____15780
                                                                    =
                                                                    let uu____15781
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____15782
                                                                    =
                                                                    let uu____15793
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15793,
                                                                    uu____15795)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15781
                                                                    uu____15782
                                                                     in
                                                                    (uu____15780,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15772
                                                                     in
                                                                    [uu____15771]
                                                                     in
                                                                    uu____15733
                                                                    ::
                                                                    uu____15768
                                                                     in
                                                                    uu____15725
                                                                    ::
                                                                    uu____15730
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15722
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15719
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15716
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15713
                                                             in
                                                          FStar_List.append
                                                            uu____15684
                                                            uu____15710
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15681
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15678
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15675
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
           (fun uu____15833  ->
              fun se  ->
                match uu____15833 with
                | (g,env1) ->
                    let uu____15853 = encode_sigelt env1 se  in
                    (match uu____15853 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15921 =
        match uu____15921 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15958 ->
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
                 ((let uu____15966 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15966
                   then
                     let uu____15971 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15973 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15975 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15971 uu____15973 uu____15975
                   else ());
                  (let uu____15980 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____15980 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15998 =
                         let uu____16006 =
                           let uu____16008 =
                             let uu____16010 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____16010
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____16008  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____16006
                          in
                       (match uu____15998 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____16030 = FStar_Options.log_queries ()
                                 in
                              if uu____16030
                              then
                                let uu____16033 =
                                  let uu____16035 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____16037 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____16039 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16035 uu____16037 uu____16039
                                   in
                                FStar_Pervasives_Native.Some uu____16033
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
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____16063,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____16083 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____16083 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16110 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16110 with | (uu____16137,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____16153 'Auu____16154 .
    ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____16153 *
      'Auu____16154) Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
        Prims.list)
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____16227  ->
              match uu____16227 with
              | (l,uu____16240,uu____16241) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____16292  ->
              match uu____16292 with
              | (l,uu____16307,uu____16308) ->
                  let uu____16319 =
                    FStar_All.pipe_left
                      (fun _0_4  -> FStar_SMTEncoding_Term.Echo _0_4)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____16322 =
                    let uu____16325 =
                      let uu____16326 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____16326  in
                    [uu____16325]  in
                  uu____16319 :: uu____16322))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____16355 =
      let uu____16358 =
        let uu____16359 = FStar_Util.psmap_empty ()  in
        let uu____16374 = FStar_Util.psmap_empty ()  in
        let uu____16377 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16381 =
          let uu____16383 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16383 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____16359;
          FStar_SMTEncoding_Env.fvar_bindings = uu____16374;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____16377;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____16381;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____16358]  in
    FStar_ST.op_Colon_Equals last_env uu____16355
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____16425 = FStar_ST.op_Bang last_env  in
      match uu____16425 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16453 ->
          let uu___394_16456 = e  in
          let uu____16457 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___394_16456.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___394_16456.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___394_16456.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___394_16456.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___394_16456.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___394_16456.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___394_16456.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___394_16456.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____16457;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___394_16456.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____16465 = FStar_ST.op_Bang last_env  in
    match uu____16465 with
    | [] -> failwith "Empty env stack"
    | uu____16492::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____16524  ->
    let uu____16525 = FStar_ST.op_Bang last_env  in
    match uu____16525 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top = copy_env hd1  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____16585  ->
    let uu____16586 = FStar_ST.op_Bang last_env  in
    match uu____16586 with
    | [] -> failwith "Popping an empty stack"
    | uu____16613::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____16650  -> FStar_Common.snapshot push_env last_env () 
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
      (fun uu____16703  ->
         let uu____16704 = snapshot_env ()  in
         match uu____16704 with
         | (env_depth,()) ->
             let uu____16726 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____16726 with
              | (varops_depth,()) ->
                  let uu____16748 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____16748 with
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
        (fun uu____16806  ->
           let uu____16807 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____16807 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____16902 = snapshot msg  in () 
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
        | (uu____16948::uu____16949,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___395_16957 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___395_16957.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___395_16957.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___395_16957.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16958 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____16978 =
        let uu____16981 =
          let uu____16982 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16982  in
        let uu____16983 = open_fact_db_tags env  in uu____16981 ::
          uu____16983
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16978
  
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
      let uu____17010 = encode_sigelt env se  in
      match uu____17010 with
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
        let uu____17055 = FStar_Options.log_queries ()  in
        if uu____17055
        then
          let uu____17060 =
            let uu____17061 =
              let uu____17063 =
                let uu____17065 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____17065 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____17063  in
            FStar_SMTEncoding_Term.Caption uu____17061  in
          uu____17060 :: decls
        else decls  in
      (let uu____17084 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____17084
       then
         let uu____17087 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____17087
       else ());
      (let env =
         let uu____17093 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____17093 tcenv  in
       let uu____17094 = encode_top_level_facts env se  in
       match uu____17094 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____17108 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____17108)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let uu____17122 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ())
         in
      if uu____17122
      then ()
      else
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         (let uu____17137 =
            FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
          if uu____17137
          then
            let uu____17140 =
              FStar_All.pipe_right
                (FStar_List.length modul.FStar_Syntax_Syntax.exports)
                Prims.string_of_int
               in
            FStar_Util.print2
              "+++++++++++Encoding externals for %s ... %s exports\n" name
              uu____17140
          else ());
         (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
          let encode_signature env1 ses =
            FStar_All.pipe_right ses
              (FStar_List.fold_left
                 (fun uu____17186  ->
                    fun se  ->
                      match uu____17186 with
                      | (g,env2) ->
                          let uu____17206 = encode_top_level_facts env2 se
                             in
                          (match uu____17206 with
                           | (g',env3) -> ((FStar_List.append g g'), env3)))
                 ([], env1))
             in
          let uu____17229 =
            encode_signature
              (let uu___396_17238 = env  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___396_17238.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___396_17238.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___396_17238.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___396_17238.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = false;
                 FStar_SMTEncoding_Env.cache =
                   (uu___396_17238.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___396_17238.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___396_17238.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___396_17238.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___396_17238.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___396_17238.FStar_SMTEncoding_Env.encoding_quantifier)
               }) modul.FStar_Syntax_Syntax.exports
             in
          match uu____17229 with
          | (decls,env1) ->
              let caption decls1 =
                let uu____17258 = FStar_Options.log_queries ()  in
                if uu____17258
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
                 (let uu___397_17275 = env1  in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___397_17275.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___397_17275.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___397_17275.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv =
                      (uu___397_17275.FStar_SMTEncoding_Env.tcenv);
                    FStar_SMTEncoding_Env.warn = true;
                    FStar_SMTEncoding_Env.cache =
                      (uu___397_17275.FStar_SMTEncoding_Env.cache);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___397_17275.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___397_17275.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___397_17275.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___397_17275.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___397_17275.FStar_SMTEncoding_Env.encoding_quantifier)
                  });
               (let uu____17278 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
                if uu____17278
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
        (let uu____17343 =
           let uu____17345 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____17345.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17343);
        (let env =
           let uu____17347 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____17347 tcenv  in
         let uu____17348 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____17387 = aux rest  in
                 (match uu____17387 with
                  | (out,rest1) ->
                      let t =
                        let uu____17415 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____17415 with
                        | FStar_Pervasives_Native.Some uu____17418 ->
                            let uu____17419 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____17419
                              x.FStar_Syntax_Syntax.sort
                        | uu____17420 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Simplify;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____17424 =
                        let uu____17427 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___398_17430 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___398_17430.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___398_17430.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____17427 :: out  in
                      (uu____17424, rest1))
             | uu____17435 -> ([], bindings)  in
           let uu____17442 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____17442 with
           | (closing,bindings) ->
               let uu____17469 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____17469, bindings)
            in
         match uu____17348 with
         | (q1,bindings) ->
             let uu____17500 = encode_env_bindings env bindings  in
             (match uu____17500 with
              | (env_decls,env1) ->
                  ((let uu____17522 =
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
                    if uu____17522
                    then
                      let uu____17529 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17529
                    else ());
                   (let uu____17534 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____17534 with
                    | (phi,qdecls) ->
                        let uu____17555 =
                          let uu____17560 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17560 phi
                           in
                        (match uu____17555 with
                         | (labels,phi1) ->
                             let uu____17577 = encode_labels labels  in
                             (match uu____17577 with
                              | (label_prefix,label_suffix) ->
                                  let caption =
                                    let uu____17614 =
                                      FStar_Options.log_queries ()  in
                                    if uu____17614
                                    then
                                      let uu____17619 =
                                        let uu____17620 =
                                          let uu____17622 =
                                            FStar_Syntax_Print.term_to_string
                                              q1
                                             in
                                          Prims.strcat
                                            "Encoding query formula: "
                                            uu____17622
                                           in
                                        FStar_SMTEncoding_Term.Caption
                                          uu____17620
                                         in
                                      [uu____17619]
                                    else []  in
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix
                                         (FStar_List.append qdecls caption))
                                     in
                                  let qry =
                                    let uu____17631 =
                                      let uu____17639 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____17640 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____17639,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17640)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17631
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
  