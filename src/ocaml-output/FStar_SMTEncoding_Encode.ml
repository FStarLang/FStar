open Prims
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term, Prims.int,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term, Prims.int,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let (prims : prims_t) =
  let uu____119 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____119 with
  | (asym, a) ->
      let uu____126 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____126 with
       | (xsym, x) ->
           let uu____133 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort in
           (match uu____133 with
            | (ysym, y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____187 =
                      let uu____198 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____198, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____187 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____224 =
                      let uu____231 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____231) in
                    FStar_SMTEncoding_Util.mkApp uu____224 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars in
                  let uu____244 =
                    let uu____247 =
                      let uu____250 =
                        let uu____253 =
                          let uu____254 =
                            let uu____261 =
                              let uu____262 =
                                let uu____273 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____273) in
                              FStar_SMTEncoding_Util.mkForall uu____262 in
                            (uu____261, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____254 in
                        let uu____290 =
                          let uu____293 =
                            let uu____294 =
                              let uu____301 =
                                let uu____302 =
                                  let uu____313 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____313) in
                                FStar_SMTEncoding_Util.mkForall uu____302 in
                              (uu____301,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____294 in
                          [uu____293] in
                        uu____253 :: uu____290 in
                      xtok_decl :: uu____250 in
                    xname_decl :: uu____247 in
                  (xtok1, (FStar_List.length vars), uu____244) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____411 =
                    let uu____427 =
                      let uu____440 =
                        let uu____441 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____441 in
                      quant axy uu____440 in
                    (FStar_Parser_Const.op_Eq, uu____427) in
                  let uu____453 =
                    let uu____471 =
                      let uu____487 =
                        let uu____500 =
                          let uu____501 =
                            let uu____502 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____502 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____501 in
                        quant axy uu____500 in
                      (FStar_Parser_Const.op_notEq, uu____487) in
                    let uu____514 =
                      let uu____532 =
                        let uu____548 =
                          let uu____561 =
                            let uu____562 =
                              let uu____563 =
                                let uu____568 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____569 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____568, uu____569) in
                              FStar_SMTEncoding_Util.mkLT uu____563 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____562 in
                          quant xy uu____561 in
                        (FStar_Parser_Const.op_LT, uu____548) in
                      let uu____581 =
                        let uu____599 =
                          let uu____615 =
                            let uu____628 =
                              let uu____629 =
                                let uu____630 =
                                  let uu____635 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____636 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____635, uu____636) in
                                FStar_SMTEncoding_Util.mkLTE uu____630 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____629 in
                            quant xy uu____628 in
                          (FStar_Parser_Const.op_LTE, uu____615) in
                        let uu____648 =
                          let uu____666 =
                            let uu____682 =
                              let uu____695 =
                                let uu____696 =
                                  let uu____697 =
                                    let uu____702 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____703 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____702, uu____703) in
                                  FStar_SMTEncoding_Util.mkGT uu____697 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____696 in
                              quant xy uu____695 in
                            (FStar_Parser_Const.op_GT, uu____682) in
                          let uu____715 =
                            let uu____733 =
                              let uu____749 =
                                let uu____762 =
                                  let uu____763 =
                                    let uu____764 =
                                      let uu____769 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____770 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____769, uu____770) in
                                    FStar_SMTEncoding_Util.mkGTE uu____764 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____763 in
                                quant xy uu____762 in
                              (FStar_Parser_Const.op_GTE, uu____749) in
                            let uu____782 =
                              let uu____800 =
                                let uu____816 =
                                  let uu____829 =
                                    let uu____830 =
                                      let uu____831 =
                                        let uu____836 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____837 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____836, uu____837) in
                                      FStar_SMTEncoding_Util.mkSub uu____831 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____830 in
                                  quant xy uu____829 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____816) in
                              let uu____849 =
                                let uu____867 =
                                  let uu____883 =
                                    let uu____896 =
                                      let uu____897 =
                                        let uu____898 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____898 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____897 in
                                    quant qx uu____896 in
                                  (FStar_Parser_Const.op_Minus, uu____883) in
                                let uu____910 =
                                  let uu____928 =
                                    let uu____944 =
                                      let uu____957 =
                                        let uu____958 =
                                          let uu____959 =
                                            let uu____964 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____965 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____964, uu____965) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____959 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____958 in
                                      quant xy uu____957 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____944) in
                                  let uu____977 =
                                    let uu____995 =
                                      let uu____1011 =
                                        let uu____1024 =
                                          let uu____1025 =
                                            let uu____1026 =
                                              let uu____1031 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____1032 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____1031, uu____1032) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1026 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1025 in
                                        quant xy uu____1024 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1011) in
                                    let uu____1044 =
                                      let uu____1062 =
                                        let uu____1078 =
                                          let uu____1091 =
                                            let uu____1092 =
                                              let uu____1093 =
                                                let uu____1098 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____1099 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____1098, uu____1099) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1093 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1092 in
                                          quant xy uu____1091 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1078) in
                                      let uu____1111 =
                                        let uu____1129 =
                                          let uu____1145 =
                                            let uu____1158 =
                                              let uu____1159 =
                                                let uu____1160 =
                                                  let uu____1165 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____1166 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____1165, uu____1166) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1160 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1159 in
                                            quant xy uu____1158 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1145) in
                                        let uu____1178 =
                                          let uu____1196 =
                                            let uu____1212 =
                                              let uu____1225 =
                                                let uu____1226 =
                                                  let uu____1227 =
                                                    let uu____1232 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____1233 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____1232, uu____1233) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1227 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1226 in
                                              quant xy uu____1225 in
                                            (FStar_Parser_Const.op_And,
                                              uu____1212) in
                                          let uu____1245 =
                                            let uu____1263 =
                                              let uu____1279 =
                                                let uu____1292 =
                                                  let uu____1293 =
                                                    let uu____1294 =
                                                      let uu____1299 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____1300 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____1299,
                                                        uu____1300) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1294 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1293 in
                                                quant xy uu____1292 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1279) in
                                            let uu____1312 =
                                              let uu____1330 =
                                                let uu____1346 =
                                                  let uu____1359 =
                                                    let uu____1360 =
                                                      let uu____1361 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1361 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1360 in
                                                  quant qx uu____1359 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1346) in
                                              [uu____1330] in
                                            uu____1263 :: uu____1312 in
                                          uu____1196 :: uu____1245 in
                                        uu____1129 :: uu____1178 in
                                      uu____1062 :: uu____1111 in
                                    uu____995 :: uu____1044 in
                                  uu____928 :: uu____977 in
                                uu____867 :: uu____910 in
                              uu____800 :: uu____849 in
                            uu____733 :: uu____782 in
                          uu____666 :: uu____715 in
                        uu____599 :: uu____648 in
                      uu____532 :: uu____581 in
                    uu____471 :: uu____514 in
                  uu____411 :: uu____453 in
                let mk1 l v1 =
                  let uu____1632 =
                    let uu____1643 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1713 ->
                              match uu____1713 with
                              | (l', uu____1729) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____1643
                      (FStar_Option.map
                         (fun uu____1805 ->
                            match uu____1805 with | (uu____1828, b) -> b v1)) in
                  FStar_All.pipe_right uu____1632 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____1919 ->
                          match uu____1919 with
                          | (l', uu____1935) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let (pretype_axiom :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string, FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun tapp ->
      fun vars ->
        let uu____1985 =
          FStar_SMTEncoding_Env.fresh_fvar "x"
            FStar_SMTEncoding_Term.Term_sort in
        match uu____1985 with
        | (xxsym, xx) ->
            let uu____1992 =
              FStar_SMTEncoding_Env.fresh_fvar "f"
                FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____1992 with
             | (ffsym, ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name =
                   env.FStar_SMTEncoding_Env.current_module_name in
                 let uu____2002 =
                   let uu____2009 =
                     let uu____2010 =
                       let uu____2021 =
                         let uu____2022 =
                           let uu____2027 =
                             let uu____2028 =
                               let uu____2033 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____2033) in
                             FStar_SMTEncoding_Util.mkEq uu____2028 in
                           (xx_has_type, uu____2027) in
                         FStar_SMTEncoding_Util.mkImp uu____2022 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____2021) in
                     FStar_SMTEncoding_Util.mkForall uu____2010 in
                   let uu____2058 =
                     let uu____2059 =
                       let uu____2060 =
                         let uu____2061 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____2061 in
                       Prims.strcat module_name uu____2060 in
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                       uu____2059 in
                   (uu____2009, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____2058) in
                 FStar_SMTEncoding_Util.mkAssume uu____2002)
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____2111 =
      let uu____2112 =
        let uu____2119 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____2119, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____2112 in
    let uu____2122 =
      let uu____2125 =
        let uu____2126 =
          let uu____2133 =
            let uu____2134 =
              let uu____2145 =
                let uu____2146 =
                  let uu____2151 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____2151) in
                FStar_SMTEncoding_Util.mkImp uu____2146 in
              ([[typing_pred]], [xx], uu____2145) in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2134 in
          (uu____2133, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____2126 in
      [uu____2125] in
    uu____2111 :: uu____2122 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____2199 =
      let uu____2200 =
        let uu____2207 =
          let uu____2208 =
            let uu____2219 =
              let uu____2224 =
                let uu____2227 = FStar_SMTEncoding_Term.boxBool b in
                [uu____2227] in
              [uu____2224] in
            let uu____2232 =
              let uu____2233 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____2233 tt in
            (uu____2219, [bb], uu____2232) in
          FStar_SMTEncoding_Util.mkForall uu____2208 in
        (uu____2207, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____2200 in
    let uu____2254 =
      let uu____2257 =
        let uu____2258 =
          let uu____2265 =
            let uu____2266 =
              let uu____2277 =
                let uu____2278 =
                  let uu____2283 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____2283) in
                FStar_SMTEncoding_Util.mkImp uu____2278 in
              ([[typing_pred]], [xx], uu____2277) in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2266 in
          (uu____2265, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____2258 in
      [uu____2257] in
    uu____2199 :: uu____2254 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____2339 =
        let uu____2340 =
          let uu____2347 =
            let uu____2350 =
              let uu____2353 =
                let uu____2356 = FStar_SMTEncoding_Term.boxInt a in
                let uu____2357 =
                  let uu____2360 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____2360] in
                uu____2356 :: uu____2357 in
              tt :: uu____2353 in
            tt :: uu____2350 in
          ("Prims.Precedes", uu____2347) in
        FStar_SMTEncoding_Util.mkApp uu____2340 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2339 in
    let precedes_y_x =
      let uu____2364 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2364 in
    let uu____2367 =
      let uu____2368 =
        let uu____2375 =
          let uu____2376 =
            let uu____2387 =
              let uu____2392 =
                let uu____2395 = FStar_SMTEncoding_Term.boxInt b in
                [uu____2395] in
              [uu____2392] in
            let uu____2400 =
              let uu____2401 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____2401 tt in
            (uu____2387, [bb], uu____2400) in
          FStar_SMTEncoding_Util.mkForall uu____2376 in
        (uu____2375, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____2368 in
    let uu____2422 =
      let uu____2425 =
        let uu____2426 =
          let uu____2433 =
            let uu____2434 =
              let uu____2445 =
                let uu____2446 =
                  let uu____2451 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____2451) in
                FStar_SMTEncoding_Util.mkImp uu____2446 in
              ([[typing_pred]], [xx], uu____2445) in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2434 in
          (uu____2433, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____2426 in
      let uu____2476 =
        let uu____2479 =
          let uu____2480 =
            let uu____2487 =
              let uu____2488 =
                let uu____2499 =
                  let uu____2500 =
                    let uu____2505 =
                      let uu____2506 =
                        let uu____2509 =
                          let uu____2512 =
                            let uu____2515 =
                              let uu____2516 =
                                let uu____2521 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____2522 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____2521, uu____2522) in
                              FStar_SMTEncoding_Util.mkGT uu____2516 in
                            let uu____2523 =
                              let uu____2526 =
                                let uu____2527 =
                                  let uu____2532 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____2533 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____2532, uu____2533) in
                                FStar_SMTEncoding_Util.mkGTE uu____2527 in
                              let uu____2534 =
                                let uu____2537 =
                                  let uu____2538 =
                                    let uu____2543 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____2544 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____2543, uu____2544) in
                                  FStar_SMTEncoding_Util.mkLT uu____2538 in
                                [uu____2537] in
                              uu____2526 :: uu____2534 in
                            uu____2515 :: uu____2523 in
                          typing_pred_y :: uu____2512 in
                        typing_pred :: uu____2509 in
                      FStar_SMTEncoding_Util.mk_and_l uu____2506 in
                    (uu____2505, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____2500 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2499) in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2488 in
            (uu____2487,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____2480 in
        [uu____2479] in
      uu____2425 :: uu____2476 in
    uu____2367 :: uu____2422 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____2596 =
      let uu____2597 =
        let uu____2604 =
          let uu____2605 =
            let uu____2616 =
              let uu____2621 =
                let uu____2624 = FStar_SMTEncoding_Term.boxString b in
                [uu____2624] in
              [uu____2621] in
            let uu____2629 =
              let uu____2630 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____2630 tt in
            (uu____2616, [bb], uu____2629) in
          FStar_SMTEncoding_Util.mkForall uu____2605 in
        (uu____2604, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____2597 in
    let uu____2651 =
      let uu____2654 =
        let uu____2655 =
          let uu____2662 =
            let uu____2663 =
              let uu____2674 =
                let uu____2675 =
                  let uu____2680 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____2680) in
                FStar_SMTEncoding_Util.mkImp uu____2675 in
              ([[typing_pred]], [xx], uu____2674) in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2663 in
          (uu____2662, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____2655 in
      [uu____2654] in
    uu____2596 :: uu____2651 in
  let mk_eq2_interp nm env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____2750 =
      let uu____2751 =
        let uu____2758 =
          let uu____2759 =
            let uu____2770 =
              let uu____2771 =
                let uu____2776 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____2776, valid) in
              FStar_SMTEncoding_Util.mkIff uu____2771 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____2770) in
          FStar_SMTEncoding_Util.mkForall uu____2759 in
        (uu____2758, (FStar_Pervasives_Native.Some "Eq2 interpretation"), nm) in
      FStar_SMTEncoding_Util.mkAssume uu____2751 in
    [uu____2750] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____2855 =
      let uu____2856 =
        let uu____2863 =
          let uu____2864 =
            let uu____2875 =
              let uu____2876 =
                let uu____2881 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____2881, valid) in
              FStar_SMTEncoding_Util.mkIff uu____2876 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____2875) in
          FStar_SMTEncoding_Util.mkForall uu____2864 in
        (uu____2863, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____2856 in
    [uu____2855] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____2937 =
      let uu____2938 =
        let uu____2945 =
          let uu____2946 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____2946 range_ty in
        let uu____2947 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const" in
        (uu____2945, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____2947) in
      FStar_SMTEncoding_Util.mkAssume uu____2938 in
    [uu____2937] in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____2987 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____2987 x1 t in
      let uu____2988 =
        let uu____2999 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____2999) in
      FStar_SMTEncoding_Util.mkForall uu____2988 in
    let uu____3022 =
      let uu____3023 =
        let uu____3030 =
          let uu____3031 =
            let uu____3042 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____3042) in
          FStar_SMTEncoding_Util.mkForall uu____3031 in
        (uu____3030,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____3023 in
    [uu____3022] in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e]) in
    let uu____3098 =
      let uu____3099 =
        let uu____3106 =
          let uu____3107 =
            let uu____3122 =
              let uu____3123 =
                let uu____3128 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____3129 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____3128, uu____3129) in
              FStar_SMTEncoding_Util.mkAnd uu____3123 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3122) in
          FStar_SMTEncoding_Util.mkForall' uu____3107 in
        (uu____3106,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____3099 in
    [uu____3098] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.t_eq2_lid, (mk_eq2_interp "t_eq2-interp"));
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env ->
    fun t ->
      fun s ->
        fun tt ->
          let uu____3391 =
            FStar_Util.find_opt
              (fun uu____3423 ->
                 match uu____3423 with
                 | (l, uu____3435) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____3391 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (uu____3469, f) -> f env s tt
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env ->
    fun fv ->
      fun t ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____3520 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env in
        match uu____3520 with
        | (form, decls) ->
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
              (FStar_SMTEncoding_Term.decl Prims.list,
                FStar_SMTEncoding_Env.env_t) FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted ->
    fun env ->
      fun fv ->
        fun tt ->
          fun t_norm ->
            fun quals ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____3572 =
                ((let uu____3575 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____3575) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____3572
              then
                let arg_sorts =
                  let uu____3585 =
                    let uu____3586 = FStar_Syntax_Subst.compress t_norm in
                    uu____3586.FStar_Syntax_Syntax.n in
                  match uu____3585 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders, uu____3592) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____3622 ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____3627 -> [] in
                let arity = FStar_List.length arg_sorts in
                let uu____3629 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity in
                match uu____3629 with
                | (vname, vtok, env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    ([d; dd], env1)
              else
                (let uu____3662 = prims.is lid in
                 if uu____3662
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid in
                   let uu____3670 = prims.mk lid vname in
                   match uu____3670 with
                   | (tok, arity, definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____3697 =
                      let uu____3708 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm in
                      match uu____3708 with
                      | (args, comp) ->
                          let comp1 =
                            let uu____3726 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp in
                            if uu____3726
                            then
                              let uu____3727 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___85_3730 =
                                     env.FStar_SMTEncoding_Env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___85_3730.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___85_3730.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___85_3730.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___85_3730.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___85_3730.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___85_3730.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___85_3730.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___85_3730.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___85_3730.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___85_3730.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___85_3730.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___85_3730.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___85_3730.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___85_3730.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___85_3730.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___85_3730.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___85_3730.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___85_3730.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___85_3730.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___85_3730.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___85_3730.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___85_3730.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___85_3730.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___85_3730.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___85_3730.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___85_3730.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___85_3730.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___85_3730.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___85_3730.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___85_3730.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___85_3730.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___85_3730.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___85_3730.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___85_3730.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___85_3730.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___85_3730.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____3727
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____3742 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1 in
                            (args, uu____3742)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____3697 with
                    | (formals, (pre_opt, res_t)) ->
                        let arity = FStar_List.length formals in
                        let uu____3792 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity in
                        (match uu____3792 with
                         | (vname, vtok, env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____3817 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___74_3867 ->
                                       match uu___74_3867 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____3871 =
                                             FStar_Util.prefix vars in
                                           (match uu____3871 with
                                            | (uu____3892,
                                               (xxsym, uu____3894)) ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____3912 =
                                                  let uu____3913 =
                                                    let uu____3920 =
                                                      let uu____3921 =
                                                        let uu____3932 =
                                                          let uu____3933 =
                                                            let uu____3938 =
                                                              let uu____3939
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____3939 in
                                                            (vapp,
                                                              uu____3938) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____3933 in
                                                        ([[vapp]], vars,
                                                          uu____3932) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____3921 in
                                                    (uu____3920,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____3913 in
                                                [uu____3912])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d, f) ->
                                           let uu____3958 =
                                             FStar_Util.prefix vars in
                                           (match uu____3958 with
                                            | (uu____3979,
                                               (xxsym, uu____3981)) ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  } in
                                                let tp_name =
                                                  FStar_SMTEncoding_Env.mk_term_projector_name
                                                    d f1 in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx]) in
                                                let uu____4004 =
                                                  let uu____4005 =
                                                    let uu____4012 =
                                                      let uu____4013 =
                                                        let uu____4024 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____4024) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4013 in
                                                    (uu____4012,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4005 in
                                                [uu____4004])
                                       | uu____4041 -> [])) in
                             let uu____4042 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1 in
                             (match uu____4042 with
                              | (vars, guards, env', decls1, uu____4069) ->
                                  let uu____4082 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None ->
                                        let uu____4091 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____4091, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____4093 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env' in
                                        (match uu____4093 with
                                         | (g, ds) ->
                                             let uu____4104 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____4104,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____4082 with
                                   | (guard, decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars in
                                       let vapp =
                                         let uu____4117 =
                                           let uu____4124 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____4124) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____4117 in
                                       let uu____4133 =
                                         let vname_decl =
                                           let uu____4141 =
                                             let uu____4152 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____4162 ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____4152,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____4141 in
                                         let uu____4171 =
                                           let env2 =
                                             let uu___86_4177 = env1 in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___86_4177.FStar_SMTEncoding_Env.encoding_quantifier)
                                             } in
                                           let uu____4178 =
                                             let uu____4179 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt in
                                             Prims.op_Negation uu____4179 in
                                           if uu____4178
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____4171 with
                                         | (tok_typing, decls2) ->
                                             let uu____4193 =
                                               match formals with
                                               | [] ->
                                                   let tok_typing1 =
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname)) in
                                                   let uu____4213 =
                                                     let uu____4214 =
                                                       let uu____4217 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_18 ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____4217 in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____4214 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____4213)
                                               | uu____4226 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_app_0 =
                                                     let uu____4233 =
                                                       let uu____4240 =
                                                         FStar_List.hd vars in
                                                       [uu____4240] in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____4233 in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____4247 =
                                                       let uu____4258 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp) in
                                                       ([[pat]], vars,
                                                         uu____4258) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____4247 in
                                                   let name_tok_corr =
                                                     let uu____4270 =
                                                       let uu____4277 =
                                                         name_tok_corr_formula
                                                           vtok_app in
                                                       (uu____4277,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____4270 in
                                                   let tok_typing1 =
                                                     let ff =
                                                       ("ty",
                                                         FStar_SMTEncoding_Term.Term_sort) in
                                                     let f =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         ff in
                                                     let vtok_app_l =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         vtok_tm [ff] in
                                                     let vtok_app_r =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         f
                                                         [(vtok,
                                                            FStar_SMTEncoding_Term.Term_sort)] in
                                                     let guarded_tok_typing =
                                                       let uu____4306 =
                                                         let uu____4317 =
                                                           let uu____4318 =
                                                             let uu____4323 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing in
                                                             let uu____4324 =
                                                               name_tok_corr_formula
                                                                 vapp in
                                                             (uu____4323,
                                                               uu____4324) in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____4318 in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____4317) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____4306 in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (guarded_tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname)) in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____4193 with
                                              | (tok_decl, env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____4133 with
                                        | (decls2, env2) ->
                                            let uu____4377 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____4385 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env' in
                                              match uu____4385 with
                                              | (encoded_res_t, decls) ->
                                                  let uu____4398 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t, uu____4398,
                                                    decls) in
                                            (match uu____4377 with
                                             | (encoded_res_t, ty_pred,
                                                decls3) ->
                                                 let typingAx =
                                                   let uu____4409 =
                                                     let uu____4416 =
                                                       let uu____4417 =
                                                         let uu____4428 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____4428) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____4417 in
                                                     (uu____4416,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____4409 in
                                                 let freshness =
                                                   let uu____4444 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____4444
                                                   then
                                                     let uu____4449 =
                                                       let uu____4450 =
                                                         let uu____4461 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____4472 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             () in
                                                         (vname, uu____4461,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____4472) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____4450 in
                                                     let uu____4475 =
                                                       let uu____4478 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____4478] in
                                                     uu____4449 :: uu____4475
                                                   else [] in
                                                 let g =
                                                   let uu____4483 =
                                                     let uu____4486 =
                                                       let uu____4489 =
                                                         let uu____4492 =
                                                           let uu____4495 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____4495 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____4492 in
                                                       FStar_List.append
                                                         decls3 uu____4489 in
                                                     FStar_List.append decls2
                                                       uu____4486 in
                                                   FStar_List.append decls11
                                                     uu____4483 in
                                                 (g, env2))))))))
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding,
            FStar_SMTEncoding_Term.decl Prims.list,
            FStar_SMTEncoding_Env.env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun x ->
      fun t ->
        fun t_norm ->
          let uu____4528 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____4528 with
          | FStar_Pervasives_Native.None ->
              let uu____4539 = encode_free_var false env x t t_norm [] in
              (match uu____4539 with
               | (decls, env1) ->
                   let fvb =
                     FStar_SMTEncoding_Env.lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
let (encode_top_level_val :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,
              FStar_SMTEncoding_Env.env_t) FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted ->
    fun env ->
      fun lid ->
        fun t ->
          fun quals ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t in
            let uu____4602 = encode_free_var uninterpreted env lid t tt quals in
            match uu____4602 with
            | (decls, env1) ->
                let uu____4621 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____4621
                then
                  let uu____4628 =
                    let uu____4631 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____4631 in
                  (uu____4628, env1)
                else (decls, env1)
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list, FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bindings ->
      fun quals ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____4689 ->
                fun lb ->
                  match uu____4689 with
                  | (decls, env1) ->
                      let uu____4709 =
                        let uu____4716 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____4716
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____4709 with
                       | (decls', env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____4739 = FStar_Syntax_Util.head_and_args t in
    match uu____4739 with
    | (hd1, args) ->
        let uu____4776 =
          let uu____4777 = FStar_Syntax_Util.un_uinst hd1 in
          uu____4777.FStar_Syntax_Syntax.n in
        (match uu____4776 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____4781, c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____4800 -> false)
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Let_rec_unencodeable -> true | uu____4806 -> false
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool, FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list, FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun uu____4834 ->
      fun quals ->
        match uu____4834 with
        | (is_rec, bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____4918 = FStar_Util.first_N nbinders formals in
              match uu____4918 with
              | (formals1, extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____4999 ->
                         fun uu____5000 ->
                           match (uu____4999, uu____5000) with
                           | ((formal, uu____5018), (binder, uu____5020)) ->
                               let uu____5029 =
                                 let uu____5036 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____5036) in
                               FStar_Syntax_Syntax.NT uu____5029) formals1
                      binders in
                  let extra_formals1 =
                    let uu____5044 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____5075 ->
                              match uu____5075 with
                              | (x, i) ->
                                  let uu____5086 =
                                    let uu___87_5087 = x in
                                    let uu____5088 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___87_5087.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___87_5087.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5088
                                    } in
                                  (uu____5086, i))) in
                    FStar_All.pipe_right uu____5044
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____5106 =
                      let uu____5111 = FStar_Syntax_Subst.compress body in
                      let uu____5112 =
                        let uu____5113 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____5113 in
                      FStar_Syntax_Syntax.extend_app_n uu____5111 uu____5112 in
                    uu____5106 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____5182 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c in
                if uu____5182
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___88_5185 = env.FStar_SMTEncoding_Env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___88_5185.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___88_5185.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___88_5185.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___88_5185.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___88_5185.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___88_5185.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___88_5185.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___88_5185.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___88_5185.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___88_5185.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___88_5185.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___88_5185.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___88_5185.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___88_5185.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___88_5185.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___88_5185.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___88_5185.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___88_5185.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___88_5185.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___88_5185.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___88_5185.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___88_5185.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___88_5185.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___88_5185.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___88_5185.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___88_5185.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___88_5185.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___88_5185.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___88_5185.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___88_5185.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___88_5185.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___88_5185.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___88_5185.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___88_5185.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___88_5185.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___88_5185.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____5222 = FStar_Syntax_Util.abs_formals e in
                match uu____5222 with
                | (binders, body, lopt) ->
                    (match binders with
                     | uu____5286::uu____5287 ->
                         let uu____5302 =
                           let uu____5303 =
                             let uu____5306 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____5306 in
                           uu____5303.FStar_Syntax_Syntax.n in
                         (match uu____5302 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                              let uu____5349 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____5349 with
                               | (formals1, c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____5391 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____5391
                                   then
                                     let uu____5426 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____5426 with
                                      | (bs0, rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____5520 ->
                                                   fun uu____5521 ->
                                                     match (uu____5520,
                                                             uu____5521)
                                                     with
                                                     | ((x, uu____5539),
                                                        (b, uu____5541)) ->
                                                         let uu____5550 =
                                                           let uu____5557 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____5557) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____5550)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____5559 =
                                            let uu____5580 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____5580) in
                                          (uu____5559, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____5648 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____5648 with
                                        | (binders1, body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x, uu____5737) ->
                              let uu____5742 =
                                let uu____5763 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____5763 in
                              (uu____5742, true)
                          | uu____5828 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____5830 ->
                              let uu____5831 =
                                let uu____5832 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____5833 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____5832 uu____5833 in
                              failwith uu____5831)
                     | uu____5858 ->
                         let rec aux' t_norm2 =
                           let uu____5885 =
                             let uu____5886 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____5886.FStar_Syntax_Syntax.n in
                           match uu____5885 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals, c) ->
                               let uu____5927 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____5927 with
                                | (formals1, c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____5955 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____5955 with
                                     | (binders1, body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv, uu____6035)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____6040 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____6096 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____6096
               then encode_top_level_vals env bindings quals
               else
                 (let uu____6108 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____6171 ->
                            fun lb ->
                              match uu____6171 with
                              | (toks, typs, decls, env1) ->
                                  ((let uu____6226 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____6226
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____6229 =
                                      let uu____6238 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____6238
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____6229 with
                                    | (tok, decl, env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____6108 with
                  | (toks, typs, decls, env1) ->
                      let toks_fvbs = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____6363 =
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
                              (Prims.parse_int "0") rng in
                        match vars with
                        | [] -> mk_fv ()
                        | uu____6369 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None ->
                                   let uu____6377 = mk_fv () in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____6377 vars)
                            else
                              (let uu____6379 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____6379) in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____6439;
                             FStar_Syntax_Syntax.lbeff = uu____6440;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____6442;
                             FStar_Syntax_Syntax.lbpos = uu____6443;_}::[],
                           t_norm::[], fvb::[]) ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid in
                            let uu____6467 =
                              let uu____6474 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm] in
                              match uu____6474 with
                              | (tcenv', uu____6492, e_t) ->
                                  let uu____6498 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____6509 -> failwith "Impossible" in
                                  (match uu____6498 with
                                   | (e1, t_norm1) ->
                                       ((let uu___91_6525 = env2 in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___91_6525.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___91_6525.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___91_6525.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___91_6525.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___91_6525.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1)) in
                            (match uu____6467 with
                             | (env', e1, t_norm1) ->
                                 let uu____6535 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____6535 with
                                  | ((binders, body, uu____6556, t_body),
                                     curry) ->
                                      let is_prop =
                                        let uu____6568 =
                                          let uu____6569 =
                                            FStar_Syntax_Subst.compress
                                              t_body in
                                          uu____6569.FStar_Syntax_Syntax.n in
                                        match uu____6568 with
                                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                                            FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.prop_lid
                                        | uu____6573 -> false in
                                      let is_lbname_squash =
                                        match lbn with
                                        | FStar_Util.Inl uu____6575 -> false
                                        | FStar_Util.Inr fv ->
                                            (FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.squash_lid)
                                              ||
                                              (FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Parser_Const.auto_squash_lid) in
                                      ((let uu____6578 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____6578
                                        then
                                          let uu____6579 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____6580 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____6579 uu____6580
                                        else ());
                                       (let uu____6582 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____6582 with
                                        | (vars, guards, env'1, binder_decls,
                                           uu____6609) ->
                                            let body1 =
                                              let uu____6623 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1 in
                                              if uu____6623
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None) in
                                            let app =
                                              let uu____6640 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn in
                                              mk_app1 uu____6640 curry fvb
                                                vars in
                                            let uu____6641 =
                                              if
                                                is_prop &&
                                                  (Prims.op_Negation
                                                     is_lbname_squash)
                                              then
                                                ((let uu____6659 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env2.FStar_SMTEncoding_Env.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____6659
                                                  then
                                                    let uu____6660 =
                                                      FStar_Syntax_Print.lbname_to_string
                                                        lbn in
                                                    FStar_Util.print1
                                                      "is_prop %s\n"
                                                      uu____6660
                                                  else ());
                                                 (let uu____6662 =
                                                    FStar_SMTEncoding_Term.mk_Valid
                                                      app in
                                                  let uu____6663 =
                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                      body1 env'1 in
                                                  (uu____6662, uu____6663)))
                                              else
                                                (let uu____6673 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1 in
                                                 (app, uu____6673)) in
                                            (match uu____6641 with
                                             | (app1, (body2, decls2)) ->
                                                 let eqn =
                                                   let uu____6696 =
                                                     let uu____6703 =
                                                       let uu____6704 =
                                                         let uu____6715 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____6715) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____6704 in
                                                     let uu____6726 =
                                                       let uu____6729 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____6729 in
                                                     (uu____6703, uu____6726,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____6696 in
                                                 let uu____6732 =
                                                   let uu____6735 =
                                                     let uu____6738 =
                                                       let uu____6741 =
                                                         let uu____6744 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1 in
                                                         FStar_List.append
                                                           [eqn] uu____6744 in
                                                       FStar_List.append
                                                         decls2 uu____6741 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____6738 in
                                                   FStar_List.append decls1
                                                     uu____6735 in
                                                 (uu____6732, env2))))))
                        | uu____6749 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____6812 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel" in
                          (uu____6812, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____6815 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____6862 ->
                                  fun fvb ->
                                    match uu____6862 with
                                    | (gtoks, env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid in
                                        let g =
                                          let uu____6908 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____6908 in
                                        let gtok =
                                          let uu____6910 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____6910 in
                                        let env4 =
                                          let uu____6912 =
                                            let uu____6915 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_19 ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____6915 in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____6912 in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2)) in
                        match uu____6815 with
                        | (gtoks, env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____7023 t_norm
                              uu____7025 =
                              match (uu____7023, uu____7025) with
                              | ((fvb, g, gtok),
                                 { FStar_Syntax_Syntax.lbname = lbn;
                                   FStar_Syntax_Syntax.lbunivs = uvs;
                                   FStar_Syntax_Syntax.lbtyp = uu____7055;
                                   FStar_Syntax_Syntax.lbeff = uu____7056;
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs = uu____7058;
                                   FStar_Syntax_Syntax.lbpos = uu____7059;_})
                                  ->
                                  let uu____7080 =
                                    let uu____7087 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm] in
                                    match uu____7087 with
                                    | (tcenv', uu____7109, e_t) ->
                                        let uu____7115 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____7126 ->
                                              failwith "Impossible" in
                                        (match uu____7115 with
                                         | (e1, t_norm1) ->
                                             ((let uu___92_7142 = env3 in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___92_7142.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1)) in
                                  (match uu____7080 with
                                   | (env', e1, t_norm1) ->
                                       ((let uu____7157 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____7157
                                         then
                                           let uu____7158 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____7159 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____7160 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____7158 uu____7159 uu____7160
                                         else ());
                                        (let uu____7162 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1 in
                                         match uu____7162 with
                                         | ((binders, body, formals, tres),
                                            curry) ->
                                             ((let uu____7199 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____7199
                                               then
                                                 let uu____7200 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____7201 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____7202 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____7203 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____7200 uu____7201
                                                   uu____7202 uu____7203
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____7207 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____7207 with
                                               | (vars, guards, env'1,
                                                  binder_decls, uu____7238)
                                                   ->
                                                   let decl_g =
                                                     let uu____7252 =
                                                       let uu____7263 =
                                                         let uu____7266 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____7266 in
                                                       (g, uu____7263,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____7252 in
                                                   let env02 =
                                                     FStar_SMTEncoding_Env.push_zfuel_name
                                                       env01
                                                       fvb.FStar_SMTEncoding_Env.fvar_lid
                                                       g in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications")) in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars in
                                                   let app =
                                                     let uu____7291 =
                                                       let uu____7298 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____7298) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7291 in
                                                   let gsapp =
                                                     let uu____7308 =
                                                       let uu____7315 =
                                                         let uu____7318 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____7318 ::
                                                           vars_tm in
                                                       (g, uu____7315) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7308 in
                                                   let gmax =
                                                     let uu____7324 =
                                                       let uu____7331 =
                                                         let uu____7334 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____7334 ::
                                                           vars_tm in
                                                       (g, uu____7331) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7324 in
                                                   let body1 =
                                                     let uu____7340 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1 in
                                                     if uu____7340
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body in
                                                   let uu____7342 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1 in
                                                   (match uu____7342 with
                                                    | (body_tm, decls2) ->
                                                        let eqn_g =
                                                          let uu____7360 =
                                                            let uu____7367 =
                                                              let uu____7368
                                                                =
                                                                let uu____7383
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____7383) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____7368 in
                                                            let uu____7404 =
                                                              let uu____7407
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____7407 in
                                                            (uu____7367,
                                                              uu____7404,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7360 in
                                                        let eqn_f =
                                                          let uu____7411 =
                                                            let uu____7418 =
                                                              let uu____7419
                                                                =
                                                                let uu____7430
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____7430) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____7419 in
                                                            (uu____7418,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7411 in
                                                        let eqn_g' =
                                                          let uu____7444 =
                                                            let uu____7451 =
                                                              let uu____7452
                                                                =
                                                                let uu____7463
                                                                  =
                                                                  let uu____7464
                                                                    =
                                                                    let uu____7469
                                                                    =
                                                                    let uu____7470
                                                                    =
                                                                    let uu____7477
                                                                    =
                                                                    let uu____7480
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0") in
                                                                    uu____7480
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____7477) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____7470 in
                                                                    (gsapp,
                                                                    uu____7469) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____7464 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____7463) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____7452 in
                                                            (uu____7451,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7444 in
                                                        let uu____7503 =
                                                          let uu____7512 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____7512
                                                          with
                                                          | (vars1, v_guards,
                                                             env4,
                                                             binder_decls1,
                                                             uu____7541) ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____7566
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____7566
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____7571
                                                                  =
                                                                  let uu____7578
                                                                    =
                                                                    let uu____7579
                                                                    =
                                                                    let uu____7590
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____7590) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____7579 in
                                                                  (uu____7578,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____7571 in
                                                              let uu____7611
                                                                =
                                                                let uu____7618
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____7618
                                                                with
                                                                | (g_typing,
                                                                   d3) ->
                                                                    let uu____7631
                                                                    =
                                                                    let uu____7634
                                                                    =
                                                                    let uu____7635
                                                                    =
                                                                    let uu____7642
                                                                    =
                                                                    let uu____7643
                                                                    =
                                                                    let uu____7654
                                                                    =
                                                                    let uu____7655
                                                                    =
                                                                    let uu____7660
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____7660,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____7655 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____7654) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____7643 in
                                                                    (uu____7642,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____7635 in
                                                                    [uu____7634] in
                                                                    (d3,
                                                                    uu____7631) in
                                                              (match uu____7611
                                                               with
                                                               | (aux_decls,
                                                                  typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____7503
                                                         with
                                                         | (aux_decls,
                                                            g_typing) ->
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
                                                               env02)))))))) in
                            let uu____7725 =
                              let uu____7738 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____7799 ->
                                   fun uu____7800 ->
                                     match (uu____7799, uu____7800) with
                                     | ((decls2, eqns, env01),
                                        (gtok, ty, lb)) ->
                                         let uu____7925 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____7925 with
                                          | (decls', eqns', env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____7738 in
                            (match uu____7725 with
                             | (decls2, eqns, env01) ->
                                 let uu____7998 =
                                   let isDeclFun uu___75_8012 =
                                     match uu___75_8012 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____8013 -> true
                                     | uu____8024 -> false in
                                   let uu____8025 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____8025
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____7998 with
                                  | (prefix_decls, rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____8065 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___76_8069 ->
                                 match uu___76_8069 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect ->
                                     true
                                 | uu____8070 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t ->
                                   let uu____8076 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____8076))) in
                      if uu____8065
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
                         | FStar_SMTEncoding_Env.Inner_let_rec ->
                             (decls1, env1)))
             with
             | Let_rec_unencodeable ->
                 let msg =
                   let uu____8128 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____8128
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t, FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let nm =
        let uu____8189 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____8189 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____8193 = encode_sigelt' env se in
      match uu____8193 with
      | (g, env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____8209 =
                  let uu____8210 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____8210 in
                [uu____8209]
            | uu____8211 ->
                let uu____8212 =
                  let uu____8215 =
                    let uu____8216 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____8216 in
                  uu____8215 :: g in
                let uu____8217 =
                  let uu____8220 =
                    let uu____8221 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____8221 in
                  [uu____8220] in
                FStar_List.append uu____8212 uu____8217 in
          (g1, env1)
and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t, FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let is_opaque_to_smt t =
        let uu____8236 =
          let uu____8237 = FStar_Syntax_Subst.compress t in
          uu____8237.FStar_Syntax_Syntax.n in
        match uu____8236 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s, uu____8241)) -> s = "opaque_to_smt"
        | uu____8242 -> false in
      let is_uninterpreted_by_smt t =
        let uu____8249 =
          let uu____8250 = FStar_Syntax_Subst.compress t in
          uu____8250.FStar_Syntax_Syntax.n in
        match uu____8249 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s, uu____8254)) -> s = "uninterpreted_by_smt"
        | uu____8255 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8260 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____8265 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____8276 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____8279 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____8282 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8297 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8301 =
            let uu____8302 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____8302 Prims.op_Negation in
          if uu____8301
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____8330 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____8354 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ in
               match uu____8354 with
               | (formals, uu____8372) ->
                   let arity = FStar_List.length formals in
                   let uu____8390 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity in
                   (match uu____8390 with
                    | (aname, atok, env2) ->
                        let uu____8410 =
                          let uu____8415 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____8415
                            env2 in
                        (match uu____8410 with
                         | (tm, decls) ->
                             let a_decls =
                               let uu____8427 =
                                 let uu____8428 =
                                   let uu____8439 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____8455 ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____8439,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____8428 in
                               [uu____8427;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____8468 =
                               let aux uu____8524 uu____8525 =
                                 match (uu____8524, uu____8525) with
                                 | ((bv, uu____8577), (env3, acc_sorts, acc))
                                     ->
                                     let uu____8615 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv in
                                     (match uu____8615 with
                                      | (xxsym, xx, env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____8468 with
                              | (uu____8687, xs_sorts, xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____8710 =
                                      let uu____8717 =
                                        let uu____8718 =
                                          let uu____8729 =
                                            let uu____8730 =
                                              let uu____8735 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts in
                                              (app, uu____8735) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____8730 in
                                          ([[app]], xs_sorts, uu____8729) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8718 in
                                      (uu____8717,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____8710 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app =
                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                        tok_term xs_sorts in
                                    let uu____8755 =
                                      let uu____8762 =
                                        let uu____8763 =
                                          let uu____8774 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts, uu____8774) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8763 in
                                      (uu____8762,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____8755 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____8793 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____8793 with
             | (env1, decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____8821, uu____8822)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____8823 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4") in
          (match uu____8823 with | (tname, ttok, env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____8840, t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____8846 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___77_8850 ->
                      match uu___77_8850 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | FStar_Syntax_Syntax.Projector uu____8851 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____8856 -> true
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____8857 -> false)) in
            Prims.op_Negation uu____8846 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____8866 =
               let uu____8873 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____8873 env fv t quals in
             match uu____8866 with
             | (decls, env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____8888 =
                   let uu____8891 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym in
                   FStar_List.append decls uu____8891 in
                 (uu____8888, env1))
      | FStar_Syntax_Syntax.Sig_assume (l, us, f) ->
          let uu____8899 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____8899 with
           | (uu____8908, f1) ->
               let uu____8910 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env in
               (match uu____8910 with
                | (f2, decls) ->
                    let g =
                      let uu____8924 =
                        let uu____8925 =
                          let uu____8932 =
                            let uu____8935 =
                              let uu____8936 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____8936 in
                            FStar_Pervasives_Native.Some uu____8935 in
                          let uu____8937 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____8932, uu____8937) in
                        FStar_SMTEncoding_Util.mkAssume uu____8925 in
                      [uu____8924] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____8943) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____8955 =
            FStar_Util.fold_map
              (fun env1 ->
                 fun lb ->
                   let lid =
                     let uu____8973 =
                       let uu____8976 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____8976.FStar_Syntax_Syntax.fv_name in
                     uu____8973.FStar_Syntax_Syntax.v in
                   let uu____8977 =
                     let uu____8978 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____8978 in
                   if uu____8977
                   then
                     let val_decl =
                       let uu___95_9006 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___95_9006.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___95_9006.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___95_9006.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____9011 = encode_sigelt' env1 val_decl in
                     match uu____9011 with | (decls, env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____8955 with
           | (env1, decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____9039,
            { FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2p1;
              FStar_Syntax_Syntax.lbunivs = uu____9041;
              FStar_Syntax_Syntax.lbtyp = uu____9042;
              FStar_Syntax_Syntax.lbeff = uu____9043;
              FStar_Syntax_Syntax.lbdef = uu____9044;
              FStar_Syntax_Syntax.lbattrs = uu____9045;
              FStar_Syntax_Syntax.lbpos = uu____9046;_}::[]),
           uu____9047)
          when FStar_Syntax_Syntax.fv_eq_lid b2p1 FStar_Parser_Const.b2p_lid
          ->
          let uu____9070 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2p1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1") in
          (match uu____9070 with
           | (tname, ttok, env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2p_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2p", [x]) in
               let valid_b2p_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2p_x]) in
               let decls =
                 let uu____9099 =
                   let uu____9102 =
                     let uu____9103 =
                       let uu____9110 =
                         let uu____9111 =
                           let uu____9122 =
                             let uu____9123 =
                               let uu____9128 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2p_x, uu____9128) in
                             FStar_SMTEncoding_Util.mkEq uu____9123 in
                           ([[b2p_x]], [xx], uu____9122) in
                         FStar_SMTEncoding_Util.mkForall uu____9111 in
                       (uu____9110, (FStar_Pervasives_Native.Some "b2p def"),
                         "b2p_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____9103 in
                   [uu____9102] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____9099 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____9161, uu____9162) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___78_9171 ->
                  match uu___78_9171 with
                  | FStar_Syntax_Syntax.Discriminator uu____9172 -> true
                  | uu____9173 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____9176, lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l ->
                   let uu____9187 =
                     let uu____9188 = FStar_List.hd l.FStar_Ident.ns in
                     uu____9188.FStar_Ident.idText in
                   uu____9187 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___79_9192 ->
                     match uu___79_9192 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                         -> true
                     | uu____9193 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____9197) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___80_9214 ->
                  match uu___80_9214 with
                  | FStar_Syntax_Syntax.Projector uu____9215 -> true
                  | uu____9220 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____9223 = FStar_SMTEncoding_Env.try_lookup_free_var env l in
          (match uu____9223 with
           | FStar_Pervasives_Native.Some uu____9230 -> ([], env)
           | FStar_Pervasives_Native.None ->
               let se1 =
                 let uu___96_9234 = se in
                 let uu____9235 = FStar_Ident.range_of_lid l in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____9235;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___96_9234.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___96_9234.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___96_9234.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____9242) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9260) ->
          let uu____9269 = encode_sigelts env ses in
          (match uu____9269 with
           | (g, env1) ->
               let uu____9286 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___81_9309 ->
                         match uu___81_9309 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____9310;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____9311;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____9312;_}
                             -> false
                         | uu____9315 -> true)) in
               (match uu____9286 with
                | (g', inversions) ->
                    let uu____9330 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___82_9351 ->
                              match uu___82_9351 with
                              | FStar_SMTEncoding_Term.DeclFun uu____9352 ->
                                  true
                              | uu____9363 -> false)) in
                    (match uu____9330 with
                     | (decls, rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t, uu____9381, tps, k, uu____9384, datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_assumption =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___83_9401 ->
                    match uu___83_9401 with
                    | FStar_Syntax_Syntax.Assumption -> true
                    | uu____9402 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_assumption
            then
              let uu____9413 = c in
              match uu____9413 with
              | (name, args, uu____9418, uu____9419, uu____9420) ->
                  let uu____9425 =
                    let uu____9426 =
                      let uu____9437 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____9454 ->
                                match uu____9454 with
                                | (uu____9461, sort, uu____9463) -> sort)) in
                      (name, uu____9437, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____9426 in
                  [uu____9425]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____9494 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l ->
                      let uu____9500 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l in
                      FStar_All.pipe_right uu____9500 FStar_Option.isNone)) in
            if uu____9494
            then []
            else
              (let uu____9532 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort in
               match uu____9532 with
               | (xxsym, xx) ->
                   let uu____9541 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____9580 ->
                             fun l ->
                               match uu____9580 with
                               | (out, decls) ->
                                   let uu____9600 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l in
                                   (match uu____9600 with
                                    | (uu____9611, data_t) ->
                                        let uu____9613 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____9613 with
                                         | (args, res) ->
                                             let indices =
                                               let uu____9659 =
                                                 let uu____9660 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____9660.FStar_Syntax_Syntax.n in
                                               match uu____9659 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____9671, indices) ->
                                                   indices
                                               | uu____9693 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1 ->
                                                       fun uu____9717 ->
                                                         match uu____9717
                                                         with
                                                         | (x, uu____9723) ->
                                                             let uu____9724 =
                                                               let uu____9725
                                                                 =
                                                                 let uu____9732
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x in
                                                                 (uu____9732,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____9725 in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____9724)
                                                    env) in
                                             let uu____9735 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1 in
                                             (match uu____9735 with
                                              | (indices1, decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____9761 =
                                                        FStar_List.map2
                                                          (fun v1 ->
                                                             fun a ->
                                                               let uu____9777
                                                                 =
                                                                 let uu____9782
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____9782,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____9777)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____9761
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____9785 =
                                                      let uu____9786 =
                                                        let uu____9791 =
                                                          let uu____9792 =
                                                            let uu____9797 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx in
                                                            (uu____9797, eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____9792 in
                                                        (out, uu____9791) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____9786 in
                                                    (uu____9785,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____9541 with
                    | (data_ax, decls) ->
                        let uu____9810 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____9810 with
                         | (ffsym, ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____9821 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____9821 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____9825 =
                                 let uu____9832 =
                                   let uu____9833 =
                                     let uu____9844 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____9859 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____9844,
                                       uu____9859) in
                                   FStar_SMTEncoding_Util.mkForall uu____9833 in
                                 let uu____9874 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____9832,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____9874) in
                               FStar_SMTEncoding_Util.mkAssume uu____9825 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____9877 =
            let uu____9890 =
              let uu____9891 = FStar_Syntax_Subst.compress k in
              uu____9891.FStar_Syntax_Syntax.n in
            match uu____9890 with
            | FStar_Syntax_Syntax.Tm_arrow (formals, kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____9936 -> (tps, k) in
          (match uu____9877 with
           | (formals, res) ->
               let uu____9959 = FStar_Syntax_Subst.open_term formals res in
               (match uu____9959 with
                | (formals1, res1) ->
                    let uu____9970 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env in
                    (match uu____9970 with
                     | (vars, guards, env', binder_decls, uu____9995) ->
                         let arity = FStar_List.length vars in
                         let uu____10009 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity in
                         (match uu____10009 with
                          | (tname, ttok, env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____10032 =
                                  let uu____10039 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____10039) in
                                FStar_SMTEncoding_Util.mkApp uu____10032 in
                              let uu____10048 =
                                let tname_decl =
                                  let uu____10058 =
                                    let uu____10059 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____10091 ->
                                              match uu____10091 with
                                              | (n1, s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____10104 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        () in
                                    (tname, uu____10059,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____10104, false) in
                                  constructor_or_logic_type_decl uu____10058 in
                                let uu____10113 =
                                  match vars with
                                  | [] ->
                                      let uu____10126 =
                                        let uu____10127 =
                                          let uu____10130 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_20 ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____10130 in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____10127 in
                                      ([], uu____10126)
                                  | uu____10141 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____10150 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____10150 in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____10164 =
                                          let uu____10171 =
                                            let uu____10172 =
                                              let uu____10187 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____10187) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____10172 in
                                          (uu____10171,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10164 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____10113 with
                                | (tok_decls, env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____10048 with
                               | (decls, env2) ->
                                   let kindingAx =
                                     let uu____10227 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____10227 with
                                     | (k1, decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____10245 =
                                               let uu____10246 =
                                                 let uu____10253 =
                                                   let uu____10254 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____10254 in
                                                 (uu____10253,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10246 in
                                             [uu____10245]
                                           else [] in
                                         let uu____10258 =
                                           let uu____10261 =
                                             let uu____10264 =
                                               let uu____10265 =
                                                 let uu____10272 =
                                                   let uu____10273 =
                                                     let uu____10284 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____10284) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10273 in
                                                 (uu____10272,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10265 in
                                             [uu____10264] in
                                           FStar_List.append karr uu____10261 in
                                         FStar_List.append decls1 uu____10258 in
                                   let aux =
                                     let uu____10300 =
                                       let uu____10303 =
                                         inversion_axioms tapp vars in
                                       let uu____10306 =
                                         let uu____10309 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____10309] in
                                       FStar_List.append uu____10303
                                         uu____10306 in
                                     FStar_List.append kindingAx uu____10300 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d, uu____10316, uu____10317, uu____10318, uu____10319,
           uu____10320)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d, uu____10328, t, uu____10330, n_tps, uu____10332) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____10340 = FStar_Syntax_Util.arrow_formals t in
          (match uu____10340 with
           | (formals, t_res) ->
               let arity = FStar_List.length formals in
               let uu____10380 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity in
               (match uu____10380 with
                | (ddconstrsym, ddtok, env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
                    let uu____10401 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____10401 with
                     | (fuel_var, fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____10415 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____10415 with
                          | (vars, guards, env', binder_decls, names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1 ->
                                        fun x ->
                                          let projectible = true in
                                          let uu____10485 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x in
                                          (uu____10485,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____10487 =
                                  let uu____10506 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____10506, true) in
                                FStar_All.pipe_right uu____10487
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app =
                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                  ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____10545 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm in
                              (match uu____10545 with
                               | (tok_typing, decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____10557::uu____10558 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             ddtok_tm [ff] in
                                         let vtok_app_r =
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____10603 =
                                           let uu____10614 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____10614) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____10603
                                     | uu____10639 -> tok_typing in
                                   let uu____10648 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____10648 with
                                    | (vars', guards', env'', decls_formals,
                                       uu____10673) ->
                                        let uu____10686 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____10686 with
                                         | (ty_pred', decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____10717 ->
                                                   let uu____10724 =
                                                     let uu____10725 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____10725 in
                                                   [uu____10724] in
                                             let encode_elim uu____10737 =
                                               let uu____10738 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____10738 with
                                               | (head1, args) ->
                                                   let uu____10781 =
                                                     let uu____10782 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____10782.FStar_Syntax_Syntax.n in
                                                   (match uu____10781 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____10792;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____10793;_},
                                                         uu____10794)
                                                        ->
                                                        let uu____10799 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        (match uu____10799
                                                         with
                                                         | (encoded_head,
                                                            encoded_head_arity)
                                                             ->
                                                             let uu____10812
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env' in
                                                             (match uu____10812
                                                              with
                                                              | (encoded_args,
                                                                 arg_decls)
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
                                                                    uu____10861
                                                                    ->
                                                                    let uu____10862
                                                                    =
                                                                    let uu____10867
                                                                    =
                                                                    let uu____10868
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____10868 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____10867) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10862
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____10884
                                                                    =
                                                                    let uu____10885
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____10885 in
                                                                    if
                                                                    uu____10884
                                                                    then
                                                                    let uu____10898
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____10898]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                  let uu____10900
                                                                    =
                                                                    let uu____10913
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____10963
                                                                    ->
                                                                    fun
                                                                    uu____10964
                                                                    ->
                                                                    match 
                                                                    (uu____10963,
                                                                    uu____10964)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____11059
                                                                    =
                                                                    let uu____11066
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____11066 in
                                                                    (match uu____11059
                                                                    with
                                                                    | 
                                                                    (uu____11079,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____11087
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____11087
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____11089
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____11089
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____10913 in
                                                                  (match uu____10900
                                                                   with
                                                                   | 
                                                                   (uu____11104,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____11107)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____11135
                                                                    =
                                                                    let uu____11142
                                                                    =
                                                                    let uu____11143
                                                                    =
                                                                    let uu____11154
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____11165
                                                                    =
                                                                    let uu____11166
                                                                    =
                                                                    let uu____11171
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____11171) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11166 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11154,
                                                                    uu____11165) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11143 in
                                                                    (uu____11142,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11135 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____11189
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid in
                                                                    if
                                                                    uu____11189
                                                                    then
                                                                    let x =
                                                                    let uu____11195
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x" in
                                                                    (uu____11195,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____11197
                                                                    =
                                                                    let uu____11204
                                                                    =
                                                                    let uu____11205
                                                                    =
                                                                    let uu____11216
                                                                    =
                                                                    let uu____11221
                                                                    =
                                                                    let uu____11224
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____11224] in
                                                                    [uu____11221] in
                                                                    let uu____11229
                                                                    =
                                                                    let uu____11230
                                                                    =
                                                                    let uu____11235
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____11236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____11235,
                                                                    uu____11236) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11230 in
                                                                    (uu____11216,
                                                                    [x],
                                                                    uu____11229) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11205 in
                                                                    let uu____11255
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop" in
                                                                    (uu____11204,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____11255) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11197
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____11262
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v1 ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____11290
                                                                    =
                                                                    let uu____11291
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____11291
                                                                    dapp1 in
                                                                    [uu____11290]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____11262
                                                                    FStar_List.flatten in
                                                                    let uu____11298
                                                                    =
                                                                    let uu____11305
                                                                    =
                                                                    let uu____11306
                                                                    =
                                                                    let uu____11317
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____11328
                                                                    =
                                                                    let uu____11329
                                                                    =
                                                                    let uu____11334
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____11334) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11329 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11317,
                                                                    uu____11328) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11306 in
                                                                    (uu____11305,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11298) in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____11354 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        (match uu____11354
                                                         with
                                                         | (encoded_head,
                                                            encoded_head_arity)
                                                             ->
                                                             let uu____11367
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env' in
                                                             (match uu____11367
                                                              with
                                                              | (encoded_args,
                                                                 arg_decls)
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
                                                                    uu____11416
                                                                    ->
                                                                    let uu____11417
                                                                    =
                                                                    let uu____11422
                                                                    =
                                                                    let uu____11423
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11423 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11422) in
                                                                    FStar_Errors.raise_error
                                                                    uu____11417
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____11439
                                                                    =
                                                                    let uu____11440
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11440 in
                                                                    if
                                                                    uu____11439
                                                                    then
                                                                    let uu____11453
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____11453]
                                                                    else [])) in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1 in
                                                                  let uu____11455
                                                                    =
                                                                    let uu____11468
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11518
                                                                    ->
                                                                    fun
                                                                    uu____11519
                                                                    ->
                                                                    match 
                                                                    (uu____11518,
                                                                    uu____11519)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____11614
                                                                    =
                                                                    let uu____11621
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____11621 in
                                                                    (match uu____11614
                                                                    with
                                                                    | 
                                                                    (uu____11634,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____11642
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____11642
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____11644
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____11644
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____11468 in
                                                                  (match uu____11455
                                                                   with
                                                                   | 
                                                                   (uu____11659,
                                                                    arg_vars,
                                                                    elim_eqns_or_guards,
                                                                    uu____11662)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1 in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____11690
                                                                    =
                                                                    let uu____11697
                                                                    =
                                                                    let uu____11698
                                                                    =
                                                                    let uu____11709
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____11720
                                                                    =
                                                                    let uu____11721
                                                                    =
                                                                    let uu____11726
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____11726) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11721 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11709,
                                                                    uu____11720) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11698 in
                                                                    (uu____11697,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11690 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____11744
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid in
                                                                    if
                                                                    uu____11744
                                                                    then
                                                                    let x =
                                                                    let uu____11750
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x" in
                                                                    (uu____11750,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____11752
                                                                    =
                                                                    let uu____11759
                                                                    =
                                                                    let uu____11760
                                                                    =
                                                                    let uu____11771
                                                                    =
                                                                    let uu____11776
                                                                    =
                                                                    let uu____11779
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____11779] in
                                                                    [uu____11776] in
                                                                    let uu____11784
                                                                    =
                                                                    let uu____11785
                                                                    =
                                                                    let uu____11790
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____11791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____11790,
                                                                    uu____11791) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11785 in
                                                                    (uu____11771,
                                                                    [x],
                                                                    uu____11784) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11760 in
                                                                    let uu____11810
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop" in
                                                                    (uu____11759,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____11810) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11752
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____11817
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v1 ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____11845
                                                                    =
                                                                    let uu____11846
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____11846
                                                                    dapp1 in
                                                                    [uu____11845]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____11817
                                                                    FStar_List.flatten in
                                                                    let uu____11853
                                                                    =
                                                                    let uu____11860
                                                                    =
                                                                    let uu____11861
                                                                    =
                                                                    let uu____11872
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____11883
                                                                    =
                                                                    let uu____11884
                                                                    =
                                                                    let uu____11889
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____11889) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11884 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11872,
                                                                    uu____11883) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____11861 in
                                                                    (uu____11860,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11853) in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____11908 ->
                                                        ((let uu____11910 =
                                                            let uu____11915 =
                                                              let uu____11916
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____11917
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____11916
                                                                uu____11917 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____11915) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____11910);
                                                         ([], []))) in
                                             let uu____11922 = encode_elim () in
                                             (match uu____11922 with
                                              | (decls2, elim) ->
                                                  let g =
                                                    let uu____11942 =
                                                      let uu____11945 =
                                                        let uu____11948 =
                                                          let uu____11951 =
                                                            let uu____11954 =
                                                              let uu____11955
                                                                =
                                                                let uu____11966
                                                                  =
                                                                  let uu____11969
                                                                    =
                                                                    let uu____11970
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____11970 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____11969 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____11966) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____11955 in
                                                            [uu____11954] in
                                                          let uu____11975 =
                                                            let uu____11978 =
                                                              let uu____11981
                                                                =
                                                                let uu____11984
                                                                  =
                                                                  let uu____11987
                                                                    =
                                                                    let uu____11990
                                                                    =
                                                                    let uu____11993
                                                                    =
                                                                    let uu____11994
                                                                    =
                                                                    let uu____12001
                                                                    =
                                                                    let uu____12002
                                                                    =
                                                                    let uu____12013
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12013) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12002 in
                                                                    (uu____12001,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11994 in
                                                                    let uu____12026
                                                                    =
                                                                    let uu____12029
                                                                    =
                                                                    let uu____12030
                                                                    =
                                                                    let uu____12037
                                                                    =
                                                                    let uu____12038
                                                                    =
                                                                    let uu____12049
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____12060
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____12049,
                                                                    uu____12060) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12038 in
                                                                    (uu____12037,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12030 in
                                                                    [uu____12029] in
                                                                    uu____11993
                                                                    ::
                                                                    uu____12026 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____11990 in
                                                                  FStar_List.append
                                                                    uu____11987
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____11984 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____11981 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____11978 in
                                                          FStar_List.append
                                                            uu____11951
                                                            uu____11975 in
                                                        FStar_List.append
                                                          decls3 uu____11948 in
                                                      FStar_List.append
                                                        decls2 uu____11945 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____11942 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list, FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun ses ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____12106 ->
              fun se ->
                match uu____12106 with
                | (g, env1) ->
                    let uu____12126 = encode_sigelt env1 se in
                    (match uu____12126 with
                     | (g', env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t, FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bindings ->
      let encode_binding b uu____12191 =
        match uu____12191 with
        | (i, decls, env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____12223 ->
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
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____12229 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____12229
                   then
                     let uu____12230 = FStar_Syntax_Print.bv_to_string x in
                     let uu____12231 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____12232 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____12230 uu____12231 uu____12232
                   else ());
                  (let uu____12234 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1 in
                   match uu____12234 with
                   | (t, decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____12250 =
                         let uu____12257 =
                           let uu____12258 =
                             let uu____12259 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____12259
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____12258 in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____12257 in
                       (match uu____12250 with
                        | (xxsym, xx, env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____12275 = FStar_Options.log_queries () in
                              if uu____12275
                              then
                                let uu____12278 =
                                  let uu____12279 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____12280 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____12281 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____12279 uu____12280 uu____12281 in
                                FStar_Pervasives_Native.Some uu____12278
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x, (uu____12297, t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____12311 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____12311 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____12334, se, uu____12336) ->
                 let uu____12341 = encode_sigelt env1 se in
                 (match uu____12341 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____12358, se) ->
                 let uu____12364 = encode_sigelt env1 se in
                 (match uu____12364 with
                  | (g, env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____12381 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____12381 with | (uu____12404, decls, env1) -> (decls, env1)
let encode_labels :
  'Auu____12419 'Auu____12420 .
    ((Prims.string, FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,
      'Auu____12419, 'Auu____12420) FStar_Pervasives_Native.tuple3 Prims.list
      ->
      (FStar_SMTEncoding_Term.decl Prims.list,
        FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____12489 ->
              match uu____12489 with
              | (l, uu____12501, uu____12502) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____12548 ->
              match uu____12548 with
              | (l, uu____12562, uu____12563) ->
                  let uu____12572 =
                    FStar_All.pipe_left
                      (fun _0_21 -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____12573 =
                    let uu____12576 =
                      let uu____12577 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____12577 in
                    [uu____12576] in
                  uu____12572 :: uu____12573)) in
    (prefix1, suffix)
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    let uu____12628 =
      let uu____12631 =
        let uu____12632 = FStar_Util.psmap_empty () in
        let uu____12647 = FStar_Util.psmap_empty () in
        let uu____12650 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____12653 =
          let uu____12654 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____12654 FStar_Ident.string_of_lid in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____12632;
          FStar_SMTEncoding_Env.fvar_bindings = uu____12647;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____12650;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____12653;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        } in
      [uu____12631] in
    FStar_ST.op_Colon_Equals last_env uu____12628
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn ->
    fun tcenv ->
      let uu____12698 = FStar_ST.op_Bang last_env in
      match uu____12698 with
      | [] -> failwith "No env; call init first!"
      | e::uu____12735 ->
          let uu___97_12738 = e in
          let uu____12739 = FStar_Ident.string_of_lid cmn in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___97_12738.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___97_12738.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___97_12738.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___97_12738.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___97_12738.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___97_12738.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___97_12738.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___97_12738.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____12739;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___97_12738.FStar_SMTEncoding_Env.encoding_quantifier)
          }
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env ->
    let uu____12745 = FStar_ST.op_Bang last_env in
    match uu____12745 with
    | [] -> failwith "Empty env stack"
    | uu____12781::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let (push_env : unit -> unit) =
  fun uu____12822 ->
    let uu____12823 = FStar_ST.op_Bang last_env in
    match uu____12823 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache in
        let top =
          let uu___98_12867 = hd1 in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___98_12867.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___98_12867.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___98_12867.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___98_12867.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___98_12867.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = refs;
            FStar_SMTEncoding_Env.nolabels =
              (uu___98_12867.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___98_12867.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___98_12867.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___98_12867.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___98_12867.FStar_SMTEncoding_Env.encoding_quantifier)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let (pop_env : unit -> unit) =
  fun uu____12905 ->
    let uu____12906 = FStar_ST.op_Bang last_env in
    match uu____12906 with
    | [] -> failwith "Popping an empty stack"
    | uu____12942::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let (push : Prims.string -> unit) =
  fun msg ->
    push_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.push ();
    FStar_SMTEncoding_Z3.push msg
let (pop : Prims.string -> unit) =
  fun msg ->
    pop_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.pop ();
    FStar_SMTEncoding_Z3.pop msg
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env -> []
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun fact_db_ids ->
      fun d ->
        match (fact_db_ids, d) with
        | (uu____13030::uu____13031, FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___99_13039 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___99_13039.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___99_13039.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___99_13039.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____13040 -> d
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env ->
    fun lid ->
      let uu____13059 =
        let uu____13062 =
          let uu____13063 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____13063 in
        let uu____13064 = open_fact_db_tags env in uu____13062 :: uu____13064 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____13059
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list, FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun se ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____13090 = encode_sigelt env se in
      match uu____13090 with
      | (g, env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv ->
    fun se ->
      let caption decls =
        let uu____13132 = FStar_Options.log_queries () in
        if uu____13132
        then
          let uu____13135 =
            let uu____13136 =
              let uu____13137 =
                let uu____13138 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____13138 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____13137 in
            FStar_SMTEncoding_Term.Caption uu____13136 in
          uu____13135 :: decls
        else decls in
      (let uu____13149 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____13149
       then
         let uu____13150 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____13150
       else ());
      (let env =
         let uu____13153 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____13153 tcenv in
       let uu____13154 = encode_top_level_facts env se in
       match uu____13154 with
       | (decls, env1) ->
           (set_env env1;
            (let uu____13168 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____13168)))
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv ->
    fun modul ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____13184 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____13184
       then
         let uu____13185 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____13185
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____13224 ->
                 fun se ->
                   match uu____13224 with
                   | (g, env2) ->
                       let uu____13244 = encode_top_level_facts env2 se in
                       (match uu____13244 with
                        | (g', env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____13267 =
         encode_signature
           (let uu___100_13276 = env in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___100_13276.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___100_13276.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___100_13276.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___100_13276.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___100_13276.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___100_13276.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___100_13276.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___100_13276.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___100_13276.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___100_13276.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____13267 with
       | (decls, env1) ->
           let caption decls1 =
             let uu____13295 = FStar_Options.log_queries () in
             if uu____13295
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___101_13303 = env1 in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___101_13303.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___101_13303.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___101_13303.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___101_13303.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___101_13303.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___101_13303.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___101_13303.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___101_13303.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___101_13303.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___101_13303.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____13305 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____13305
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,
          FStar_SMTEncoding_ErrorReporting.label Prims.list,
          FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____13363 =
           let uu____13364 = FStar_TypeChecker_Env.current_module tcenv in
           uu____13364.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____13363);
        (let env =
           let uu____13366 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____13366 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv (fun bs -> fun b -> b :: bs)
             [] in
         let uu____13378 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____13415 = aux rest in
                 (match uu____13415 with
                  | (out, rest1) ->
                      let t =
                        let uu____13445 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____13445 with
                        | FStar_Pervasives_Native.Some uu____13450 ->
                            let uu____13451 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____13451
                              x.FStar_Syntax_Syntax.sort
                        | uu____13452 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t in
                      let uu____13456 =
                        let uu____13459 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___102_13462 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___102_13462.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___102_13462.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____13459 :: out in
                      (uu____13456, rest1))
             | uu____13467 -> ([], bindings1) in
           let uu____13474 = aux bindings in
           match uu____13474 with
           | (closing, bindings1) ->
               let uu____13499 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____13499, bindings1) in
         match uu____13378 with
         | (q1, bindings1) ->
             let uu____13522 =
               let uu____13527 =
                 FStar_List.filter
                   (fun uu___84_13532 ->
                      match uu___84_13532 with
                      | FStar_TypeChecker_Env.Binding_sig uu____13533 ->
                          false
                      | uu____13540 -> true) bindings1 in
               encode_env_bindings env uu____13527 in
             (match uu____13522 with
              | (env_decls, env1) ->
                  ((let uu____13558 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____13558
                    then
                      let uu____13559 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____13559
                    else ());
                   (let uu____13561 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1 in
                    match uu____13561 with
                    | (phi, qdecls) ->
                        let uu____13582 =
                          let uu____13587 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____13587 phi in
                        (match uu____13582 with
                         | (labels, phi1) ->
                             let uu____13604 = encode_labels labels in
                             (match uu____13604 with
                              | (label_prefix, label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____13641 =
                                      let uu____13648 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____13649 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query" in
                                      (uu____13648,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____13649) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13641 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))