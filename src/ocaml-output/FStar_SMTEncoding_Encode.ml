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
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____95 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____95 with
  | (asym,a) ->
      let uu____102 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____102 with
       | (xsym,x) ->
           let uu____109 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____109 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____162 =
                      let uu____173 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____173, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____162  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____199 =
                      let uu____206 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____206)  in
                    FStar_SMTEncoding_Util.mkApp uu____199  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____219 =
                    let uu____222 =
                      let uu____225 =
                        let uu____228 =
                          let uu____229 =
                            let uu____236 =
                              let uu____237 =
                                let uu____248 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____248)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____237
                               in
                            (uu____236, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____229  in
                        let uu____265 =
                          let uu____268 =
                            let uu____269 =
                              let uu____276 =
                                let uu____277 =
                                  let uu____288 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____288)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____277
                                 in
                              (uu____276,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____269  in
                          [uu____268]  in
                        uu____228 :: uu____265  in
                      xtok_decl :: uu____225  in
                    xname_decl :: uu____222  in
                  (xtok1, (FStar_List.length vars), uu____219)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____387 =
                    let uu____404 =
                      let uu____417 =
                        let uu____418 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____418
                         in
                      quant axy uu____417  in
                    (FStar_Parser_Const.op_Eq, uu____404)  in
                  let uu____431 =
                    let uu____450 =
                      let uu____467 =
                        let uu____480 =
                          let uu____481 =
                            let uu____482 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____482  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____481
                           in
                        quant axy uu____480  in
                      (FStar_Parser_Const.op_notEq, uu____467)  in
                    let uu____495 =
                      let uu____514 =
                        let uu____531 =
                          let uu____544 =
                            let uu____545 =
                              let uu____546 =
                                let uu____551 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____552 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____551, uu____552)  in
                              FStar_SMTEncoding_Util.mkLT uu____546  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____545
                             in
                          quant xy uu____544  in
                        (FStar_Parser_Const.op_LT, uu____531)  in
                      let uu____565 =
                        let uu____584 =
                          let uu____601 =
                            let uu____614 =
                              let uu____615 =
                                let uu____616 =
                                  let uu____621 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____622 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____621, uu____622)  in
                                FStar_SMTEncoding_Util.mkLTE uu____616  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____615
                               in
                            quant xy uu____614  in
                          (FStar_Parser_Const.op_LTE, uu____601)  in
                        let uu____635 =
                          let uu____654 =
                            let uu____671 =
                              let uu____684 =
                                let uu____685 =
                                  let uu____686 =
                                    let uu____691 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____692 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____691, uu____692)  in
                                  FStar_SMTEncoding_Util.mkGT uu____686  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____685
                                 in
                              quant xy uu____684  in
                            (FStar_Parser_Const.op_GT, uu____671)  in
                          let uu____705 =
                            let uu____724 =
                              let uu____741 =
                                let uu____754 =
                                  let uu____755 =
                                    let uu____756 =
                                      let uu____761 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____762 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____761, uu____762)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____756
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____755
                                   in
                                quant xy uu____754  in
                              (FStar_Parser_Const.op_GTE, uu____741)  in
                            let uu____775 =
                              let uu____794 =
                                let uu____811 =
                                  let uu____824 =
                                    let uu____825 =
                                      let uu____826 =
                                        let uu____831 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____832 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____831, uu____832)  in
                                      FStar_SMTEncoding_Util.mkSub uu____826
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____825
                                     in
                                  quant xy uu____824  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____811)
                                 in
                              let uu____845 =
                                let uu____864 =
                                  let uu____881 =
                                    let uu____894 =
                                      let uu____895 =
                                        let uu____896 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____896
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____895
                                       in
                                    quant qx uu____894  in
                                  (FStar_Parser_Const.op_Minus, uu____881)
                                   in
                                let uu____909 =
                                  let uu____928 =
                                    let uu____945 =
                                      let uu____958 =
                                        let uu____959 =
                                          let uu____960 =
                                            let uu____965 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____966 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____965, uu____966)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____960
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____959
                                         in
                                      quant xy uu____958  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____945)
                                     in
                                  let uu____979 =
                                    let uu____998 =
                                      let uu____1015 =
                                        let uu____1028 =
                                          let uu____1029 =
                                            let uu____1030 =
                                              let uu____1035 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1036 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1035, uu____1036)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1030
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1029
                                           in
                                        quant xy uu____1028  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1015)
                                       in
                                    let uu____1049 =
                                      let uu____1068 =
                                        let uu____1085 =
                                          let uu____1098 =
                                            let uu____1099 =
                                              let uu____1100 =
                                                let uu____1105 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1106 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1105, uu____1106)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1100
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1099
                                             in
                                          quant xy uu____1098  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1085)
                                         in
                                      let uu____1119 =
                                        let uu____1138 =
                                          let uu____1155 =
                                            let uu____1168 =
                                              let uu____1169 =
                                                let uu____1170 =
                                                  let uu____1175 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1176 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1175, uu____1176)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1170
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1169
                                               in
                                            quant xy uu____1168  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1155)
                                           in
                                        let uu____1189 =
                                          let uu____1208 =
                                            let uu____1225 =
                                              let uu____1238 =
                                                let uu____1239 =
                                                  let uu____1240 =
                                                    let uu____1245 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1246 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1245, uu____1246)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1240
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1239
                                                 in
                                              quant xy uu____1238  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1225)
                                             in
                                          let uu____1259 =
                                            let uu____1278 =
                                              let uu____1295 =
                                                let uu____1308 =
                                                  let uu____1309 =
                                                    let uu____1310 =
                                                      let uu____1315 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1316 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1315,
                                                        uu____1316)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1310
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1309
                                                   in
                                                quant xy uu____1308  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1295)
                                               in
                                            let uu____1329 =
                                              let uu____1348 =
                                                let uu____1365 =
                                                  let uu____1378 =
                                                    let uu____1379 =
                                                      let uu____1380 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1380
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1379
                                                     in
                                                  quant qx uu____1378  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1365)
                                                 in
                                              [uu____1348]  in
                                            uu____1278 :: uu____1329  in
                                          uu____1208 :: uu____1259  in
                                        uu____1138 :: uu____1189  in
                                      uu____1068 :: uu____1119  in
                                    uu____998 :: uu____1049  in
                                  uu____928 :: uu____979  in
                                uu____864 :: uu____909  in
                              uu____794 :: uu____845  in
                            uu____724 :: uu____775  in
                          uu____654 :: uu____705  in
                        uu____584 :: uu____635  in
                      uu____514 :: uu____565  in
                    uu____450 :: uu____495  in
                  uu____387 :: uu____431  in
                let mk1 l v1 =
                  let uu____1664 =
                    let uu____1675 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1749  ->
                              match uu____1749 with
                              | (l',uu____1767) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____1675
                      (FStar_Option.map
                         (fun uu____1847  ->
                            match uu____1847 with
                            | (uu____1872,b) ->
                                let _0_41 = FStar_Ident.range_of_lid l  in
                                b _0_41 v1))
                     in
                  FStar_All.pipe_right uu____1664 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____1965  ->
                          match uu____1965 with
                          | (l',uu____1983) -> FStar_Ident.lid_equals l l'))
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
          let uu____2032 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2032 with
          | (xxsym,xx) ->
              let uu____2039 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2039 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2049 =
                     let uu____2056 =
                       let uu____2057 =
                         let uu____2068 =
                           let uu____2069 =
                             let uu____2074 =
                               let uu____2075 =
                                 let uu____2080 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2080)  in
                               FStar_SMTEncoding_Util.mkEq uu____2075  in
                             (xx_has_type, uu____2074)  in
                           FStar_SMTEncoding_Util.mkImp uu____2069  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2068)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2057  in
                     let uu____2105 =
                       let uu____2106 =
                         let uu____2107 =
                           let uu____2108 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2108  in
                         Prims.strcat module_name uu____2107  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2106
                        in
                     (uu____2056, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2105)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2049)
  
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
    let uu____2144 =
      let uu____2145 =
        let uu____2152 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2152, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2145  in
    let uu____2155 =
      let uu____2158 =
        let uu____2159 =
          let uu____2166 =
            let uu____2167 =
              let uu____2178 =
                let uu____2179 =
                  let uu____2184 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2184)  in
                FStar_SMTEncoding_Util.mkImp uu____2179  in
              ([[typing_pred]], [xx], uu____2178)  in
            let uu____2207 =
              let uu____2220 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2220  in
            uu____2207 uu____2167  in
          (uu____2166, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2159  in
      [uu____2158]  in
    uu____2144 :: uu____2155  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2240 =
      let uu____2241 =
        let uu____2248 =
          let uu____2249 = FStar_TypeChecker_Env.get_range env  in
          let uu____2250 =
            let uu____2261 =
              let uu____2266 =
                let uu____2269 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2269]  in
              [uu____2266]  in
            let uu____2274 =
              let uu____2275 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2275 tt  in
            (uu____2261, [bb], uu____2274)  in
          FStar_SMTEncoding_Term.mkForall uu____2249 uu____2250  in
        (uu____2248, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2241  in
    let uu____2296 =
      let uu____2299 =
        let uu____2300 =
          let uu____2307 =
            let uu____2308 =
              let uu____2319 =
                let uu____2320 =
                  let uu____2325 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2325)  in
                FStar_SMTEncoding_Util.mkImp uu____2320  in
              ([[typing_pred]], [xx], uu____2319)  in
            let uu____2348 =
              let uu____2361 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2361  in
            uu____2348 uu____2308  in
          (uu____2307, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2300  in
      [uu____2299]  in
    uu____2240 :: uu____2296  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____2389 =
        let uu____2390 =
          let uu____2397 =
            let uu____2400 =
              let uu____2403 =
                let uu____2406 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____2407 =
                  let uu____2410 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____2410]  in
                uu____2406 :: uu____2407  in
              tt :: uu____2403  in
            tt :: uu____2400  in
          ("Prims.Precedes", uu____2397)  in
        FStar_SMTEncoding_Util.mkApp uu____2390  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2389  in
    let precedes_y_x =
      let uu____2414 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2414  in
    let uu____2417 =
      let uu____2418 =
        let uu____2425 =
          let uu____2426 = FStar_TypeChecker_Env.get_range env  in
          let uu____2427 =
            let uu____2438 =
              let uu____2443 =
                let uu____2446 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2446]  in
              [uu____2443]  in
            let uu____2451 =
              let uu____2452 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2452 tt  in
            (uu____2438, [bb], uu____2451)  in
          FStar_SMTEncoding_Term.mkForall uu____2426 uu____2427  in
        (uu____2425, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2418  in
    let uu____2473 =
      let uu____2476 =
        let uu____2477 =
          let uu____2484 =
            let uu____2485 =
              let uu____2496 =
                let uu____2497 =
                  let uu____2502 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2502)  in
                FStar_SMTEncoding_Util.mkImp uu____2497  in
              ([[typing_pred]], [xx], uu____2496)  in
            let uu____2525 =
              let uu____2538 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2538  in
            uu____2525 uu____2485  in
          (uu____2484, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2477  in
      let uu____2541 =
        let uu____2544 =
          let uu____2545 =
            let uu____2552 =
              let uu____2553 =
                let uu____2564 =
                  let uu____2565 =
                    let uu____2570 =
                      let uu____2571 =
                        let uu____2574 =
                          let uu____2577 =
                            let uu____2580 =
                              let uu____2581 =
                                let uu____2586 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2587 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2586, uu____2587)  in
                              FStar_SMTEncoding_Util.mkGT uu____2581  in
                            let uu____2588 =
                              let uu____2591 =
                                let uu____2592 =
                                  let uu____2597 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2598 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2597, uu____2598)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2592  in
                              let uu____2599 =
                                let uu____2602 =
                                  let uu____2603 =
                                    let uu____2608 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2609 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2608, uu____2609)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2603  in
                                [uu____2602]  in
                              uu____2591 :: uu____2599  in
                            uu____2580 :: uu____2588  in
                          typing_pred_y :: uu____2577  in
                        typing_pred :: uu____2574  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2571  in
                    (uu____2570, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2565  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2564)
                 in
              let uu____2636 =
                let uu____2649 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2649  in
              uu____2636 uu____2553  in
            (uu____2552,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2545  in
        [uu____2544]  in
      uu____2476 :: uu____2541  in
    uu____2417 :: uu____2473  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2669 =
      let uu____2670 =
        let uu____2677 =
          let uu____2678 = FStar_TypeChecker_Env.get_range env  in
          let uu____2679 =
            let uu____2690 =
              let uu____2695 =
                let uu____2698 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2698]  in
              [uu____2695]  in
            let uu____2703 =
              let uu____2704 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2704 tt  in
            (uu____2690, [bb], uu____2703)  in
          FStar_SMTEncoding_Term.mkForall uu____2678 uu____2679  in
        (uu____2677, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2670  in
    let uu____2725 =
      let uu____2728 =
        let uu____2729 =
          let uu____2736 =
            let uu____2737 =
              let uu____2748 =
                let uu____2749 =
                  let uu____2754 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____2754)  in
                FStar_SMTEncoding_Util.mkImp uu____2749  in
              ([[typing_pred]], [xx], uu____2748)  in
            let uu____2777 =
              let uu____2790 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2790  in
            uu____2777 uu____2737  in
          (uu____2736, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2729  in
      [uu____2728]  in
    uu____2669 :: uu____2725  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____2821 =
      let uu____2822 =
        let uu____2829 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____2829, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2822  in
    [uu____2821]  in
  let mk_and_interp env conj uu____2841 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____2866 =
      let uu____2867 =
        let uu____2874 =
          let uu____2875 = FStar_TypeChecker_Env.get_range env  in
          let uu____2876 =
            let uu____2887 =
              let uu____2888 =
                let uu____2893 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____2893, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____2888  in
            ([[l_and_a_b]], [aa; bb], uu____2887)  in
          FStar_SMTEncoding_Term.mkForall uu____2875 uu____2876  in
        (uu____2874, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2867  in
    [uu____2866]  in
  let mk_or_interp env disj uu____2931 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____2956 =
      let uu____2957 =
        let uu____2964 =
          let uu____2965 = FStar_TypeChecker_Env.get_range env  in
          let uu____2966 =
            let uu____2977 =
              let uu____2978 =
                let uu____2983 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____2983, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____2978  in
            ([[l_or_a_b]], [aa; bb], uu____2977)  in
          FStar_SMTEncoding_Term.mkForall uu____2965 uu____2966  in
        (uu____2964, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2957  in
    [uu____2956]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3046 =
      let uu____3047 =
        let uu____3054 =
          let uu____3055 = FStar_TypeChecker_Env.get_range env  in
          let uu____3056 =
            let uu____3067 =
              let uu____3068 =
                let uu____3073 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3073, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3068  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3067)  in
          FStar_SMTEncoding_Term.mkForall uu____3055 uu____3056  in
        (uu____3054, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3047  in
    [uu____3046]  in
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
    let uu____3146 =
      let uu____3147 =
        let uu____3154 =
          let uu____3155 = FStar_TypeChecker_Env.get_range env  in
          let uu____3156 =
            let uu____3167 =
              let uu____3168 =
                let uu____3173 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3173, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3168  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3167)  in
          FStar_SMTEncoding_Term.mkForall uu____3155 uu____3156  in
        (uu____3154, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3147  in
    [uu____3146]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3244 =
      let uu____3245 =
        let uu____3252 =
          let uu____3253 = FStar_TypeChecker_Env.get_range env  in
          let uu____3254 =
            let uu____3265 =
              let uu____3266 =
                let uu____3271 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3271, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3266  in
            ([[l_imp_a_b]], [aa; bb], uu____3265)  in
          FStar_SMTEncoding_Term.mkForall uu____3253 uu____3254  in
        (uu____3252, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3245  in
    [uu____3244]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3334 =
      let uu____3335 =
        let uu____3342 =
          let uu____3343 = FStar_TypeChecker_Env.get_range env  in
          let uu____3344 =
            let uu____3355 =
              let uu____3356 =
                let uu____3361 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3361, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3356  in
            ([[l_iff_a_b]], [aa; bb], uu____3355)  in
          FStar_SMTEncoding_Term.mkForall uu____3343 uu____3344  in
        (uu____3342, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3335  in
    [uu____3334]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3413 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3413  in
    let uu____3416 =
      let uu____3417 =
        let uu____3424 =
          let uu____3425 = FStar_TypeChecker_Env.get_range env  in
          let uu____3426 =
            let uu____3437 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3437)  in
          FStar_SMTEncoding_Term.mkForall uu____3425 uu____3426  in
        (uu____3424, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3417  in
    [uu____3416]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3475 =
      let uu____3476 =
        let uu____3483 =
          let uu____3484 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3484 range_ty  in
        let uu____3485 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3483, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3485)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3476  in
    [uu____3475]  in
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
        let uu____3519 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3519 x1 t  in
      let uu____3520 = FStar_TypeChecker_Env.get_range env  in
      let uu____3521 =
        let uu____3532 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3532)  in
      FStar_SMTEncoding_Term.mkForall uu____3520 uu____3521  in
    let uu____3555 =
      let uu____3556 =
        let uu____3563 =
          let uu____3564 = FStar_TypeChecker_Env.get_range env  in
          let uu____3565 =
            let uu____3576 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3576)  in
          FStar_SMTEncoding_Term.mkForall uu____3564 uu____3565  in
        (uu____3563,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3556  in
    [uu____3555]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3626 =
      let uu____3627 =
        let uu____3634 =
          let uu____3635 = FStar_TypeChecker_Env.get_range env  in
          let uu____3636 =
            let uu____3651 =
              let uu____3652 =
                let uu____3657 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3658 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3657, uu____3658)  in
              FStar_SMTEncoding_Util.mkAnd uu____3652  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3651)
             in
          FStar_SMTEncoding_Term.mkForall' uu____3635 uu____3636  in
        (uu____3634,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3627  in
    [uu____3626]  in
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
          let uu____3972 =
            FStar_Util.find_opt
              (fun uu____3998  ->
                 match uu____3998 with
                 | (l,uu____4010) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____3972 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4035,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4071 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4071 with
        | (form,decls) ->
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
              let uu____4111 =
                ((let uu____4114 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4114) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4111
              then
                let arg_sorts =
                  let uu____4124 =
                    let uu____4125 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4125.FStar_Syntax_Syntax.n  in
                  match uu____4124 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4131) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4161  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4166 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4168 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4168 with
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
                (let uu____4201 = prims.is lid  in
                 if uu____4201
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4209 = prims.mk lid vname  in
                   match uu____4209 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4236 =
                      let uu____4247 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4247 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4265 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4265
                            then
                              let uu____4266 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___82_4269 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___82_4269.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___82_4269.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___82_4269.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___82_4269.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___82_4269.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___82_4269.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___82_4269.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___82_4269.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___82_4269.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___82_4269.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___82_4269.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___82_4269.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___82_4269.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___82_4269.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___82_4269.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___82_4269.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___82_4269.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___82_4269.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___82_4269.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___82_4269.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___82_4269.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___82_4269.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___82_4269.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___82_4269.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___82_4269.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___82_4269.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___82_4269.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___82_4269.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___82_4269.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___82_4269.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___82_4269.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___82_4269.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___82_4269.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___82_4269.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___82_4269.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___82_4269.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4266
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4281 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4281)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4236 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4331 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4331 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4356 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___71_4398  ->
                                       match uu___71_4398 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4402 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4402 with
                                            | (uu____4423,(xxsym,uu____4425))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4443 =
                                                  let uu____4444 =
                                                    let uu____4451 =
                                                      let uu____4452 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4453 =
                                                        let uu____4464 =
                                                          let uu____4465 =
                                                            let uu____4470 =
                                                              let uu____4471
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4471
                                                               in
                                                            (vapp,
                                                              uu____4470)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4465
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4464)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4452 uu____4453
                                                       in
                                                    (uu____4451,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4444
                                                   in
                                                [uu____4443])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4490 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4490 with
                                            | (uu____4511,(xxsym,uu____4513))
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
                                                let uu____4536 =
                                                  let uu____4537 =
                                                    let uu____4544 =
                                                      let uu____4545 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4546 =
                                                        let uu____4557 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4557)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4545 uu____4546
                                                       in
                                                    (uu____4544,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4537
                                                   in
                                                [uu____4536])
                                       | uu____4574 -> []))
                                in
                             let uu____4575 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____4575 with
                              | (vars,guards,env',decls1,uu____4602) ->
                                  let uu____4615 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4624 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____4624, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____4626 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____4626 with
                                         | (g,ds) ->
                                             let uu____4637 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____4637,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____4615 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____4650 =
                                           let uu____4657 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____4657)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____4650
                                          in
                                       let uu____4666 =
                                         let vname_decl =
                                           let uu____4674 =
                                             let uu____4685 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____4695  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____4685,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____4674
                                            in
                                         let uu____4704 =
                                           let env2 =
                                             let uu___83_4710 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___83_4710.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____4711 =
                                             let uu____4712 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____4712  in
                                           if uu____4711
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____4704 with
                                         | (tok_typing,decls2) ->
                                             let uu____4726 =
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
                                                   let uu____4746 =
                                                     let uu____4747 =
                                                       let uu____4750 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____4750
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____4747
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____4746)
                                               | uu____4759 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____4766 =
                                                       let uu____4773 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____4773]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____4766
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____4778 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____4779 =
                                                       let uu____4790 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____4790)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____4778 uu____4779
                                                      in
                                                   let name_tok_corr =
                                                     let uu____4802 =
                                                       let uu____4809 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____4809,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____4802
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
                                                       let uu____4838 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____4839 =
                                                         let uu____4850 =
                                                           let uu____4851 =
                                                             let uu____4856 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____4857 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____4856,
                                                               uu____4857)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____4851
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____4850)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____4838
                                                         uu____4839
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
                                             (match uu____4726 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____4666 with
                                        | (decls2,env2) ->
                                            let uu____4910 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____4918 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____4918 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____4931 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____4931,
                                                    decls)
                                               in
                                            (match uu____4910 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____4942 =
                                                     let uu____4949 =
                                                       let uu____4950 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____4951 =
                                                         let uu____4962 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____4962)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____4950
                                                         uu____4951
                                                        in
                                                     (uu____4949,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____4942
                                                    in
                                                 let freshness =
                                                   let uu____4978 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____4978
                                                   then
                                                     let uu____4983 =
                                                       let uu____4984 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____4985 =
                                                         let uu____4996 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5007 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____4996,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5007)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____4984
                                                         uu____4985
                                                        in
                                                     let uu____5010 =
                                                       let uu____5013 =
                                                         let uu____5014 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5014 env2
                                                           vapp vars
                                                          in
                                                       [uu____5013]  in
                                                     uu____4983 :: uu____5010
                                                   else []  in
                                                 let g =
                                                   let uu____5019 =
                                                     let uu____5022 =
                                                       let uu____5025 =
                                                         let uu____5028 =
                                                           let uu____5031 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5031
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5028
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5025
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5022
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5019
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5056 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5056 with
          | FStar_Pervasives_Native.None  ->
              let uu____5067 = encode_free_var false env x t t_norm []  in
              (match uu____5067 with
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
        FStar_Syntax_Syntax.term ->
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
            let uu____5120 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5120 with
            | (decls,env1) ->
                let uu____5139 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5139
                then
                  let uu____5146 =
                    let uu____5149 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5149  in
                  (uu____5146, env1)
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
             (fun uu____5201  ->
                fun lb  ->
                  match uu____5201 with
                  | (decls,env1) ->
                      let uu____5221 =
                        let uu____5228 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5228
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5221 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5249 = FStar_Syntax_Util.head_and_args t  in
    match uu____5249 with
    | (hd1,args) ->
        let uu____5286 =
          let uu____5287 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5287.FStar_Syntax_Syntax.n  in
        (match uu____5286 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5291,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5310 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5314 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5336  ->
      fun quals  ->
        match uu____5336 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5412 = FStar_Util.first_N nbinders formals  in
              match uu____5412 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____5493  ->
                         fun uu____5494  ->
                           match (uu____5493, uu____5494) with
                           | ((formal,uu____5512),(binder,uu____5514)) ->
                               let uu____5523 =
                                 let uu____5530 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____5530)  in
                               FStar_Syntax_Syntax.NT uu____5523) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____5538 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____5569  ->
                              match uu____5569 with
                              | (x,i) ->
                                  let uu____5580 =
                                    let uu___84_5581 = x  in
                                    let uu____5582 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___84_5581.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___84_5581.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5582
                                    }  in
                                  (uu____5580, i)))
                       in
                    FStar_All.pipe_right uu____5538
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____5600 =
                      let uu____5601 = FStar_Syntax_Subst.compress body  in
                      let uu____5602 =
                        let uu____5603 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____5603
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____5601 uu____5602
                       in
                    uu____5600 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____5664 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____5664
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___85_5667 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___85_5667.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___85_5667.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___85_5667.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___85_5667.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___85_5667.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___85_5667.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___85_5667.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___85_5667.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___85_5667.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___85_5667.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___85_5667.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___85_5667.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___85_5667.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___85_5667.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___85_5667.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___85_5667.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___85_5667.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___85_5667.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___85_5667.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___85_5667.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___85_5667.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___85_5667.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___85_5667.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___85_5667.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___85_5667.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___85_5667.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___85_5667.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___85_5667.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___85_5667.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___85_5667.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___85_5667.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___85_5667.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___85_5667.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___85_5667.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___85_5667.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___85_5667.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____5700 = FStar_Syntax_Util.abs_formals e  in
                match uu____5700 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____5764::uu____5765 ->
                         let uu____5780 =
                           let uu____5781 =
                             let uu____5784 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____5784
                              in
                           uu____5781.FStar_Syntax_Syntax.n  in
                         (match uu____5780 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____5827 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____5827 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____5869 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____5869
                                   then
                                     let uu____5904 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____5904 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____5998  ->
                                                   fun uu____5999  ->
                                                     match (uu____5998,
                                                             uu____5999)
                                                     with
                                                     | ((x,uu____6017),
                                                        (b,uu____6019)) ->
                                                         let uu____6028 =
                                                           let uu____6035 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6035)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6028)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6037 =
                                            let uu____6058 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6058)  in
                                          (uu____6037, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6126 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6126 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6215) ->
                              let uu____6220 =
                                let uu____6241 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6241  in
                              (uu____6220, true)
                          | uu____6306 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____6308 ->
                              let uu____6309 =
                                let uu____6310 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6311 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6310 uu____6311
                                 in
                              failwith uu____6309)
                     | uu____6336 ->
                         let rec aux' t_norm2 =
                           let uu____6361 =
                             let uu____6362 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6362.FStar_Syntax_Syntax.n  in
                           match uu____6361 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6403 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6403 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____6431 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____6431 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____6511) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____6516 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____6572 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____6572
               then encode_top_level_vals env bindings quals
               else
                 (let uu____6584 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____6647  ->
                            fun lb  ->
                              match uu____6647 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____6702 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____6702
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____6705 =
                                      let uu____6714 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____6714
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____6705 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____6584 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____6829 =
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
                        | uu____6835 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____6843 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____6843 vars)
                            else
                              (let uu____6845 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____6845)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____6897;
                             FStar_Syntax_Syntax.lbeff = uu____6898;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____6900;
                             FStar_Syntax_Syntax.lbpos = uu____6901;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____6925 =
                              let uu____6932 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____6932 with
                              | (tcenv',uu____6950,e_t) ->
                                  let uu____6956 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____6967 -> failwith "Impossible"  in
                                  (match uu____6956 with
                                   | (e1,t_norm1) ->
                                       ((let uu___88_6983 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___88_6983.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___88_6983.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___88_6983.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___88_6983.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___88_6983.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____6925 with
                             | (env',e1,t_norm1) ->
                                 let uu____6993 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____6993 with
                                  | ((binders,body,uu____7014,t_body),curry)
                                      ->
                                      ((let uu____7026 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7026
                                        then
                                          let uu____7027 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7028 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7027 uu____7028
                                        else ());
                                       (let uu____7030 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7030 with
                                        | (vars,guards,env'1,binder_decls,uu____7057)
                                            ->
                                            let body1 =
                                              let uu____7071 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7071
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None)
                                               in
                                            let app =
                                              let uu____7088 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7088 curry fvb
                                                vars
                                               in
                                            let uu____7089 =
                                              let uu____7098 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7098
                                              then
                                                let uu____7109 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7110 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7109, uu____7110)
                                              else
                                                (let uu____7120 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7120))
                                               in
                                            (match uu____7089 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7143 =
                                                     let uu____7150 =
                                                       let uu____7151 =
                                                         FStar_Syntax_Util.range_of_lbname
                                                           lbn
                                                          in
                                                       let uu____7152 =
                                                         let uu____7163 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7163)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7151
                                                         uu____7152
                                                        in
                                                     let uu____7174 =
                                                       let uu____7177 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7177
                                                        in
                                                     (uu____7150, uu____7174,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7143
                                                    in
                                                 let uu____7180 =
                                                   let uu____7183 =
                                                     let uu____7186 =
                                                       let uu____7189 =
                                                         let uu____7192 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7192
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7189
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7186
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7183
                                                    in
                                                 (uu____7180, env2))))))
                        | uu____7197 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7252 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7252, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7255 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7302  ->
                                  fun fvb  ->
                                    match uu____7302 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7348 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7348
                                           in
                                        let gtok =
                                          let uu____7350 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7350
                                           in
                                        let env4 =
                                          let uu____7352 =
                                            let uu____7355 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____7355
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7352
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7255 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____7455 t_norm
                              uu____7457 =
                              match (uu____7455, uu____7457) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____7487;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____7488;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____7490;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____7491;_})
                                  ->
                                  let uu____7512 =
                                    let uu____7519 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____7519 with
                                    | (tcenv',uu____7541,e_t) ->
                                        let uu____7547 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____7558 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____7547 with
                                         | (e1,t_norm1) ->
                                             ((let uu___89_7574 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___89_7574.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____7512 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____7589 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____7589
                                         then
                                           let uu____7590 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____7591 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____7592 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____7590 uu____7591 uu____7592
                                         else ());
                                        (let uu____7594 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____7594 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____7631 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____7631
                                               then
                                                 let uu____7632 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____7633 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____7634 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____7635 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____7632 uu____7633
                                                   uu____7634 uu____7635
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____7639 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____7639 with
                                               | (vars,guards,env'1,binder_decls,uu____7670)
                                                   ->
                                                   let decl_g =
                                                     let uu____7684 =
                                                       let uu____7695 =
                                                         let uu____7698 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____7698
                                                          in
                                                       (g, uu____7695,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____7684
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
                                                     let uu____7723 =
                                                       let uu____7730 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____7730)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7723
                                                      in
                                                   let gsapp =
                                                     let uu____7740 =
                                                       let uu____7747 =
                                                         let uu____7750 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____7750 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____7747)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7740
                                                      in
                                                   let gmax =
                                                     let uu____7756 =
                                                       let uu____7763 =
                                                         let uu____7766 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____7766 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____7763)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____7756
                                                      in
                                                   let body1 =
                                                     let uu____7772 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____7772
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____7774 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____7774 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____7792 =
                                                            let uu____7799 =
                                                              let uu____7800
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____7801
                                                                =
                                                                let uu____7816
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____7816)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall'
                                                                uu____7800
                                                                uu____7801
                                                               in
                                                            let uu____7837 =
                                                              let uu____7840
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____7840
                                                               in
                                                            (uu____7799,
                                                              uu____7837,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7792
                                                           in
                                                        let eqn_f =
                                                          let uu____7844 =
                                                            let uu____7851 =
                                                              let uu____7852
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____7853
                                                                =
                                                                let uu____7864
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____7864)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____7852
                                                                uu____7853
                                                               in
                                                            (uu____7851,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7844
                                                           in
                                                        let eqn_g' =
                                                          let uu____7878 =
                                                            let uu____7885 =
                                                              let uu____7886
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____7887
                                                                =
                                                                let uu____7898
                                                                  =
                                                                  let uu____7899
                                                                    =
                                                                    let uu____7904
                                                                    =
                                                                    let uu____7905
                                                                    =
                                                                    let uu____7912
                                                                    =
                                                                    let uu____7915
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____7915
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____7912)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____7905
                                                                     in
                                                                    (gsapp,
                                                                    uu____7904)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____7899
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____7898)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____7886
                                                                uu____7887
                                                               in
                                                            (uu____7885,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7878
                                                           in
                                                        let uu____7938 =
                                                          let uu____7947 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____7947
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____7976)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____8001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8001
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8006
                                                                  =
                                                                  let uu____8013
                                                                    =
                                                                    let uu____8014
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8015
                                                                    =
                                                                    let uu____8026
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8026)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8014
                                                                    uu____8015
                                                                     in
                                                                  (uu____8013,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8006
                                                                 in
                                                              let uu____8047
                                                                =
                                                                let uu____8054
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8054
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8067
                                                                    =
                                                                    let uu____8070
                                                                    =
                                                                    let uu____8071
                                                                    =
                                                                    let uu____8078
                                                                    =
                                                                    let uu____8079
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8080
                                                                    =
                                                                    let uu____8091
                                                                    =
                                                                    let uu____8092
                                                                    =
                                                                    let uu____8097
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8097,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8092
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8091)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8079
                                                                    uu____8080
                                                                     in
                                                                    (uu____8078,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8071
                                                                     in
                                                                    [uu____8070]
                                                                     in
                                                                    (d3,
                                                                    uu____8067)
                                                                 in
                                                              (match uu____8047
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____7938
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
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
                                                               env02))))))))
                               in
                            let uu____8162 =
                              let uu____8175 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8236  ->
                                   fun uu____8237  ->
                                     match (uu____8236, uu____8237) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8362 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8362 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8175
                               in
                            (match uu____8162 with
                             | (decls2,eqns,env01) ->
                                 let uu____8435 =
                                   let isDeclFun uu___72_8447 =
                                     match uu___72_8447 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____8448 -> true
                                     | uu____8459 -> false  in
                                   let uu____8460 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____8460
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____8435 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____8500 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___73_8504  ->
                                 match uu___73_8504 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____8505 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____8511 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____8511)))
                         in
                      if uu____8500
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
                         | FStar_SMTEncoding_Env.Inner_let_rec  ->
                             (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____8563 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____8563
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
        let uu____8612 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____8612 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____8616 = encode_sigelt' env se  in
      match uu____8616 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____8632 =
                  let uu____8633 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____8633  in
                [uu____8632]
            | uu____8634 ->
                let uu____8635 =
                  let uu____8638 =
                    let uu____8639 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____8639  in
                  uu____8638 :: g  in
                let uu____8640 =
                  let uu____8643 =
                    let uu____8644 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____8644  in
                  [uu____8643]  in
                FStar_List.append uu____8635 uu____8640
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
        let uu____8657 =
          let uu____8658 = FStar_Syntax_Subst.compress t  in
          uu____8658.FStar_Syntax_Syntax.n  in
        match uu____8657 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____8662)) -> s = "opaque_to_smt"
        | uu____8663 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____8668 =
          let uu____8669 = FStar_Syntax_Subst.compress t  in
          uu____8669.FStar_Syntax_Syntax.n  in
        match uu____8668 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____8673)) -> s = "uninterpreted_by_smt"
        | uu____8674 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8679 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____8684 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____8695 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____8698 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____8701 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____8716 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____8720 =
            let uu____8721 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____8721 Prims.op_Negation  in
          if uu____8720
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____8747 ->
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
               let uu____8767 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____8767 with
               | (formals,uu____8785) ->
                   let arity = FStar_List.length formals  in
                   let uu____8803 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____8803 with
                    | (aname,atok,env2) ->
                        let uu____8823 =
                          let uu____8828 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____8828
                            env2
                           in
                        (match uu____8823 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____8840 =
                                 let uu____8841 =
                                   let uu____8852 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____8868  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____8852,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____8841
                                  in
                               [uu____8840;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____8881 =
                               let aux uu____8933 uu____8934 =
                                 match (uu____8933, uu____8934) with
                                 | ((bv,uu____8986),(env3,acc_sorts,acc)) ->
                                     let uu____9024 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9024 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____8881 with
                              | (uu____9096,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9119 =
                                      let uu____9126 =
                                        let uu____9127 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9128 =
                                          let uu____9139 =
                                            let uu____9140 =
                                              let uu____9145 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9145)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9140
                                             in
                                          ([[app]], xs_sorts, uu____9139)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9127 uu____9128
                                         in
                                      (uu____9126,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9119
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
                                    let uu____9165 =
                                      let uu____9172 =
                                        let uu____9173 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9174 =
                                          let uu____9185 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9185)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9173 uu____9174
                                         in
                                      (uu____9172,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9165
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9204 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9204 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9232,uu____9233) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9234 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9234 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9251,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9257 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___74_9261  ->
                      match uu___74_9261 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9262 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9267 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9268 -> false))
               in
            Prims.op_Negation uu____9257  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9277 =
               let uu____9284 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9284 env fv t quals  in
             match uu____9277 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9299 =
                   let uu____9302 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9302  in
                 (uu____9299, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9310 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9310 with
           | (uu____9319,f1) ->
               let uu____9321 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env  in
               (match uu____9321 with
                | (f2,decls) ->
                    let g =
                      let uu____9335 =
                        let uu____9336 =
                          let uu____9343 =
                            let uu____9346 =
                              let uu____9347 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9347
                               in
                            FStar_Pervasives_Native.Some uu____9346  in
                          let uu____9348 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____9343, uu____9348)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9336  in
                      [uu____9335]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9354) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____9366 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____9384 =
                       let uu____9387 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____9387.FStar_Syntax_Syntax.fv_name  in
                     uu____9384.FStar_Syntax_Syntax.v  in
                   let uu____9388 =
                     let uu____9389 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____9389  in
                   if uu____9388
                   then
                     let val_decl =
                       let uu___92_9417 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___92_9417.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___92_9417.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___92_9417.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____9422 = encode_sigelt' env1 val_decl  in
                     match uu____9422 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____9366 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____9450,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                         FStar_Syntax_Syntax.lbunivs = uu____9452;
                         FStar_Syntax_Syntax.lbtyp = uu____9453;
                         FStar_Syntax_Syntax.lbeff = uu____9454;
                         FStar_Syntax_Syntax.lbdef = uu____9455;
                         FStar_Syntax_Syntax.lbattrs = uu____9456;
                         FStar_Syntax_Syntax.lbpos = uu____9457;_}::[]),uu____9458)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____9481 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____9481 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____9510 =
                   let uu____9513 =
                     let uu____9514 =
                       let uu____9521 =
                         let uu____9522 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____9523 =
                           let uu____9534 =
                             let uu____9535 =
                               let uu____9540 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____9540)  in
                             FStar_SMTEncoding_Util.mkEq uu____9535  in
                           ([[b2t_x]], [xx], uu____9534)  in
                         FStar_SMTEncoding_Term.mkForall uu____9522
                           uu____9523
                          in
                       (uu____9521, (FStar_Pervasives_Native.Some "b2t def"),
                         "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____9514  in
                   [uu____9513]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____9510
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____9573,uu____9574) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___75_9583  ->
                  match uu___75_9583 with
                  | FStar_Syntax_Syntax.Discriminator uu____9584 -> true
                  | uu____9585 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____9588,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____9599 =
                     let uu____9600 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____9600.FStar_Ident.idText  in
                   uu____9599 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___76_9604  ->
                     match uu___76_9604 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____9605 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____9609) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___77_9626  ->
                  match uu___77_9626 with
                  | FStar_Syntax_Syntax.Projector uu____9627 -> true
                  | uu____9632 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____9635 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____9635 with
           | FStar_Pervasives_Native.Some uu____9642 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___93_9646 = se  in
                 let uu____9647 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____9647;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___93_9646.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___93_9646.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___93_9646.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____9654) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9672) ->
          let uu____9681 = encode_sigelts env ses  in
          (match uu____9681 with
           | (g,env1) ->
               let uu____9698 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___78_9721  ->
                         match uu___78_9721 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____9722;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____9723;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____9724;_}
                             -> false
                         | uu____9727 -> true))
                  in
               (match uu____9698 with
                | (g',inversions) ->
                    let uu____9742 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___79_9763  ->
                              match uu___79_9763 with
                              | FStar_SMTEncoding_Term.DeclFun uu____9764 ->
                                  true
                              | uu____9775 -> false))
                       in
                    (match uu____9742 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____9793,tps,k,uu____9796,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___80_9813  ->
                    match uu___80_9813 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____9814 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____9823 = c  in
              match uu____9823 with
              | (name,args,uu____9828,uu____9829,uu____9830) ->
                  let uu____9835 =
                    let uu____9836 =
                      let uu____9847 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____9864  ->
                                match uu____9864 with
                                | (uu____9871,sort,uu____9873) -> sort))
                         in
                      (name, uu____9847, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____9836  in
                  [uu____9835]
            else
              (let uu____9879 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____9879 c)
             in
          let inversion_axioms tapp vars =
            let uu____9901 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____9907 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____9907 FStar_Option.isNone))
               in
            if uu____9901
            then []
            else
              (let uu____9939 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____9939 with
               | (xxsym,xx) ->
                   let uu____9948 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____9987  ->
                             fun l  ->
                               match uu____9987 with
                               | (out,decls) ->
                                   let uu____10007 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10007 with
                                    | (uu____10018,data_t) ->
                                        let uu____10020 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10020 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10066 =
                                                 let uu____10067 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10067.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10066 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10078,indices) ->
                                                   indices
                                               | uu____10100 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10124  ->
                                                         match uu____10124
                                                         with
                                                         | (x,uu____10130) ->
                                                             let uu____10131
                                                               =
                                                               let uu____10132
                                                                 =
                                                                 let uu____10139
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10139,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10132
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10131)
                                                    env)
                                                in
                                             let uu____10142 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10142 with
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
                                                      let uu____10168 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10184
                                                                 =
                                                                 let uu____10189
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10189,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10184)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10168
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10192 =
                                                      let uu____10193 =
                                                        let uu____10198 =
                                                          let uu____10199 =
                                                            let uu____10204 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10204,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10199
                                                           in
                                                        (out, uu____10198)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10193
                                                       in
                                                    (uu____10192,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____9948 with
                    | (data_ax,decls) ->
                        let uu____10217 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10217 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10228 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10228 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10232 =
                                 let uu____10239 =
                                   let uu____10240 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____10241 =
                                     let uu____10252 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10267 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10252,
                                       uu____10267)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____10240 uu____10241
                                    in
                                 let uu____10282 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10239,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10282)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10232
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10285 =
            let uu____10298 =
              let uu____10299 = FStar_Syntax_Subst.compress k  in
              uu____10299.FStar_Syntax_Syntax.n  in
            match uu____10298 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10344 -> (tps, k)  in
          (match uu____10285 with
           | (formals,res) ->
               let uu____10367 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____10367 with
                | (formals1,res1) ->
                    let uu____10378 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____10378 with
                     | (vars,guards,env',binder_decls,uu____10403) ->
                         let arity = FStar_List.length vars  in
                         let uu____10417 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____10417 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____10440 =
                                  let uu____10447 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____10447)  in
                                FStar_SMTEncoding_Util.mkApp uu____10440  in
                              let uu____10456 =
                                let tname_decl =
                                  let uu____10466 =
                                    let uu____10467 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____10499  ->
                                              match uu____10499 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____10512 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____10467,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____10512, false)
                                     in
                                  constructor_or_logic_type_decl uu____10466
                                   in
                                let uu____10521 =
                                  match vars with
                                  | [] ->
                                      let uu____10534 =
                                        let uu____10535 =
                                          let uu____10538 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____10538
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____10535
                                         in
                                      ([], uu____10534)
                                  | uu____10549 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____10558 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____10558
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____10572 =
                                          let uu____10579 =
                                            let uu____10580 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____10581 =
                                              let uu____10596 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____10596)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____10580 uu____10581
                                             in
                                          (uu____10579,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10572
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____10521 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____10456 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____10636 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____10636 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____10654 =
                                               let uu____10655 =
                                                 let uu____10662 =
                                                   let uu____10663 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____10663
                                                    in
                                                 (uu____10662,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10655
                                                in
                                             [uu____10654]
                                           else []  in
                                         let uu____10667 =
                                           let uu____10670 =
                                             let uu____10673 =
                                               let uu____10674 =
                                                 let uu____10681 =
                                                   let uu____10682 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____10683 =
                                                     let uu____10694 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____10694)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____10682 uu____10683
                                                    in
                                                 (uu____10681,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____10674
                                                in
                                             [uu____10673]  in
                                           FStar_List.append karr uu____10670
                                            in
                                         FStar_List.append decls1 uu____10667
                                      in
                                   let aux =
                                     let uu____10710 =
                                       let uu____10713 =
                                         inversion_axioms tapp vars  in
                                       let uu____10716 =
                                         let uu____10719 =
                                           let uu____10720 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____10720 env2
                                             tapp vars
                                            in
                                         [uu____10719]  in
                                       FStar_List.append uu____10713
                                         uu____10716
                                        in
                                     FStar_List.append kindingAx uu____10710
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____10727,uu____10728,uu____10729,uu____10730,uu____10731)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____10739,t,uu____10741,n_tps,uu____10743) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____10751 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____10751 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____10791 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____10791 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____10812 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____10812 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____10826 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____10826 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____10896 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____10896,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____10898 =
                                  let uu____10917 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____10917, true)
                                   in
                                let uu____10926 =
                                  let uu____10947 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____10947
                                   in
                                FStar_All.pipe_right uu____10898 uu____10926
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
                              let uu____10978 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____10978 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____10990::uu____10991 ->
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
                                         let uu____11036 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____11037 =
                                           let uu____11048 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11048)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11036 uu____11037
                                     | uu____11073 -> tok_typing  in
                                   let uu____11082 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11082 with
                                    | (vars',guards',env'',decls_formals,uu____11107)
                                        ->
                                        let uu____11120 =
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
                                        (match uu____11120 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11151 ->
                                                   let uu____11158 =
                                                     let uu____11159 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11159
                                                      in
                                                   [uu____11158]
                                                in
                                             let encode_elim uu____11169 =
                                               let uu____11170 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11170 with
                                               | (head1,args) ->
                                                   let uu____11213 =
                                                     let uu____11214 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11214.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11213 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11224;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11225;_},uu____11226)
                                                        ->
                                                        let uu____11231 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11231
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11244
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11244
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
                                                                    uu____11287
                                                                    ->
                                                                    let uu____11288
                                                                    =
                                                                    let uu____11293
                                                                    =
                                                                    let uu____11294
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11294
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11293)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11288
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11310
                                                                    =
                                                                    let uu____11311
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11311
                                                                     in
                                                                    if
                                                                    uu____11310
                                                                    then
                                                                    let uu____11324
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11324]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11326
                                                                    =
                                                                    let uu____11339
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11389
                                                                     ->
                                                                    fun
                                                                    uu____11390
                                                                     ->
                                                                    match 
                                                                    (uu____11389,
                                                                    uu____11390)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____11485
                                                                    =
                                                                    let uu____11492
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____11492
                                                                     in
                                                                    (match uu____11485
                                                                    with
                                                                    | 
                                                                    (uu____11505,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____11513
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____11513
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____11515
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____11515
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
                                                                    uu____11339
                                                                     in
                                                                  (match uu____11326
                                                                   with
                                                                   | 
                                                                   (uu____11530,arg_vars,elim_eqns_or_guards,uu____11533)
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
                                                                    let uu____11561
                                                                    =
                                                                    let uu____11568
                                                                    =
                                                                    let uu____11569
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____11570
                                                                    =
                                                                    let uu____11581
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____11592
                                                                    =
                                                                    let uu____11593
                                                                    =
                                                                    let uu____11598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____11598)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11593
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11581,
                                                                    uu____11592)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11569
                                                                    uu____11570
                                                                     in
                                                                    (uu____11568,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11561
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____11616
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____11616
                                                                    then
                                                                    let x =
                                                                    let uu____11622
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____11622,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____11624
                                                                    =
                                                                    let uu____11631
                                                                    =
                                                                    let uu____11632
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____11633
                                                                    =
                                                                    let uu____11644
                                                                    =
                                                                    let uu____11649
                                                                    =
                                                                    let uu____11652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____11652]
                                                                     in
                                                                    [uu____11649]
                                                                     in
                                                                    let uu____11657
                                                                    =
                                                                    let uu____11658
                                                                    =
                                                                    let uu____11663
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____11664
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____11663,
                                                                    uu____11664)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11658
                                                                     in
                                                                    (uu____11644,
                                                                    [x],
                                                                    uu____11657)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11632
                                                                    uu____11633
                                                                     in
                                                                    let uu____11683
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____11631,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____11683)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11624
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____11690
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
                                                                    (let uu____11718
                                                                    =
                                                                    let uu____11719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____11719
                                                                    dapp1  in
                                                                    [uu____11718])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____11690
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____11726
                                                                    =
                                                                    let uu____11733
                                                                    =
                                                                    let uu____11734
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____11735
                                                                    =
                                                                    let uu____11746
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____11757
                                                                    =
                                                                    let uu____11758
                                                                    =
                                                                    let uu____11763
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____11763)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____11758
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____11746,
                                                                    uu____11757)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____11734
                                                                    uu____11735
                                                                     in
                                                                    (uu____11733,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____11726)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____11783 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11783
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11796
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11796
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
                                                                    uu____11839
                                                                    ->
                                                                    let uu____11840
                                                                    =
                                                                    let uu____11845
                                                                    =
                                                                    let uu____11846
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11846
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11845)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11840
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11862
                                                                    =
                                                                    let uu____11863
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11863
                                                                     in
                                                                    if
                                                                    uu____11862
                                                                    then
                                                                    let uu____11876
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11876]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11878
                                                                    =
                                                                    let uu____11891
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11941
                                                                     ->
                                                                    fun
                                                                    uu____11942
                                                                     ->
                                                                    match 
                                                                    (uu____11941,
                                                                    uu____11942)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12037
                                                                    =
                                                                    let uu____12044
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12044
                                                                     in
                                                                    (match uu____12037
                                                                    with
                                                                    | 
                                                                    (uu____12057,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12065
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12065
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12067
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12067
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
                                                                    uu____11891
                                                                     in
                                                                  (match uu____11878
                                                                   with
                                                                   | 
                                                                   (uu____12082,arg_vars,elim_eqns_or_guards,uu____12085)
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
                                                                    let uu____12113
                                                                    =
                                                                    let uu____12120
                                                                    =
                                                                    let uu____12121
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12122
                                                                    =
                                                                    let uu____12133
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12144
                                                                    =
                                                                    let uu____12145
                                                                    =
                                                                    let uu____12150
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12150)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12145
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12133,
                                                                    uu____12144)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12121
                                                                    uu____12122
                                                                     in
                                                                    (uu____12120,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12113
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12168
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12168
                                                                    then
                                                                    let x =
                                                                    let uu____12174
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12174,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12176
                                                                    =
                                                                    let uu____12183
                                                                    =
                                                                    let uu____12184
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12185
                                                                    =
                                                                    let uu____12196
                                                                    =
                                                                    let uu____12201
                                                                    =
                                                                    let uu____12204
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12204]
                                                                     in
                                                                    [uu____12201]
                                                                     in
                                                                    let uu____12209
                                                                    =
                                                                    let uu____12210
                                                                    =
                                                                    let uu____12215
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12216
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12215,
                                                                    uu____12216)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12210
                                                                     in
                                                                    (uu____12196,
                                                                    [x],
                                                                    uu____12209)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12184
                                                                    uu____12185
                                                                     in
                                                                    let uu____12235
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12183,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12235)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12176
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12242
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
                                                                    (let uu____12270
                                                                    =
                                                                    let uu____12271
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12271
                                                                    dapp1  in
                                                                    [uu____12270])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12242
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12278
                                                                    =
                                                                    let uu____12285
                                                                    =
                                                                    let uu____12286
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12287
                                                                    =
                                                                    let uu____12298
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12309
                                                                    =
                                                                    let uu____12310
                                                                    =
                                                                    let uu____12315
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12315)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12310
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12298,
                                                                    uu____12309)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12286
                                                                    uu____12287
                                                                     in
                                                                    (uu____12285,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12278)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____12334 ->
                                                        ((let uu____12336 =
                                                            let uu____12341 =
                                                              let uu____12342
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____12343
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____12342
                                                                uu____12343
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____12341)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____12336);
                                                         ([], [])))
                                                in
                                             let uu____12348 = encode_elim ()
                                                in
                                             (match uu____12348 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____12368 =
                                                      let uu____12371 =
                                                        let uu____12374 =
                                                          let uu____12377 =
                                                            let uu____12380 =
                                                              let uu____12381
                                                                =
                                                                let uu____12392
                                                                  =
                                                                  let uu____12395
                                                                    =
                                                                    let uu____12396
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____12396
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12395
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____12392)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____12381
                                                               in
                                                            [uu____12380]  in
                                                          let uu____12401 =
                                                            let uu____12404 =
                                                              let uu____12407
                                                                =
                                                                let uu____12410
                                                                  =
                                                                  let uu____12413
                                                                    =
                                                                    let uu____12416
                                                                    =
                                                                    let uu____12419
                                                                    =
                                                                    let uu____12420
                                                                    =
                                                                    let uu____12427
                                                                    =
                                                                    let uu____12428
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12429
                                                                    =
                                                                    let uu____12440
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12440)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12428
                                                                    uu____12429
                                                                     in
                                                                    (uu____12427,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12420
                                                                     in
                                                                    let uu____12453
                                                                    =
                                                                    let uu____12456
                                                                    =
                                                                    let uu____12457
                                                                    =
                                                                    let uu____12464
                                                                    =
                                                                    let uu____12465
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12466
                                                                    =
                                                                    let uu____12477
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____12488
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____12477,
                                                                    uu____12488)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12465
                                                                    uu____12466
                                                                     in
                                                                    (uu____12464,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12457
                                                                     in
                                                                    [uu____12456]
                                                                     in
                                                                    uu____12419
                                                                    ::
                                                                    uu____12453
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____12416
                                                                     in
                                                                  FStar_List.append
                                                                    uu____12413
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____12410
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____12407
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____12404
                                                             in
                                                          FStar_List.append
                                                            uu____12377
                                                            uu____12401
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____12374
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____12371
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____12368
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
           (fun uu____12534  ->
              fun se  ->
                match uu____12534 with
                | (g,env1) ->
                    let uu____12554 = encode_sigelt env1 se  in
                    (match uu____12554 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____12611 =
        match uu____12611 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____12643 ->
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
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____12649 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____12649
                   then
                     let uu____12650 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____12651 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____12652 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____12650 uu____12651 uu____12652
                   else ());
                  (let uu____12654 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____12654 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12670 =
                         let uu____12677 =
                           let uu____12678 =
                             let uu____12679 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____12679
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____12678  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____12677
                          in
                       (match uu____12670 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____12695 = FStar_Options.log_queries ()
                                 in
                              if uu____12695
                              then
                                let uu____12698 =
                                  let uu____12699 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____12700 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____12701 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____12699 uu____12700 uu____12701
                                   in
                                FStar_Pervasives_Native.Some uu____12698
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____12717,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____12731 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____12731 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____12754,se,uu____12756) ->
                 let uu____12761 = encode_sigelt env1 se  in
                 (match uu____12761 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____12778,se) ->
                 let uu____12784 = encode_sigelt env1 se  in
                 (match uu____12784 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____12801 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____12801 with | (uu____12824,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____12836 'Auu____12837 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____12836,'Auu____12837)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____12905  ->
              match uu____12905 with
              | (l,uu____12917,uu____12918) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____12964  ->
              match uu____12964 with
              | (l,uu____12978,uu____12979) ->
                  let uu____12988 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____12989 =
                    let uu____12992 =
                      let uu____12993 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____12993  in
                    [uu____12992]  in
                  uu____12988 :: uu____12989))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____13018 =
      let uu____13021 =
        let uu____13022 = FStar_Util.psmap_empty ()  in
        let uu____13037 = FStar_Util.psmap_empty ()  in
        let uu____13040 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13043 =
          let uu____13044 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13044 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13022;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13037;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13040;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13043;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13021]  in
    FStar_ST.op_Colon_Equals last_env uu____13018
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13074 = FStar_ST.op_Bang last_env  in
      match uu____13074 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13101 ->
          let uu___94_13104 = e  in
          let uu____13105 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___94_13104.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___94_13104.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___94_13104.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___94_13104.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___94_13104.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___94_13104.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___94_13104.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___94_13104.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13105;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___94_13104.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> Prims.unit) =
  fun env  ->
    let uu____13109 = FStar_ST.op_Bang last_env  in
    match uu____13109 with
    | [] -> failwith "Empty env stack"
    | uu____13135::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____13164  ->
    let uu____13165 = FStar_ST.op_Bang last_env  in
    match uu____13165 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
        let top =
          let uu___95_13199 = hd1  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___95_13199.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___95_13199.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___95_13199.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___95_13199.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___95_13199.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = refs;
            FStar_SMTEncoding_Env.nolabels =
              (uu___95_13199.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___95_13199.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___95_13199.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___95_13199.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___95_13199.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____13225  ->
    let uu____13226 = FStar_ST.op_Bang last_env  in
    match uu____13226 with
    | [] -> failwith "Popping an empty stack"
    | uu____13252::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> Prims.unit) =
  fun msg  ->
    push_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.push ();
    FStar_SMTEncoding_Z3.push msg
  
let (pop : Prims.string -> Prims.unit) =
  fun msg  ->
    pop_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.pop ();
    FStar_SMTEncoding_Z3.pop msg
  
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
        | (uu____13316::uu____13317,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___96_13325 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___96_13325.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___96_13325.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___96_13325.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____13326 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____13341 =
        let uu____13344 =
          let uu____13345 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____13345  in
        let uu____13346 = open_fact_db_tags env  in uu____13344 ::
          uu____13346
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____13341
  
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
      let uu____13368 = encode_sigelt env se  in
      match uu____13368 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____13404 = FStar_Options.log_queries ()  in
        if uu____13404
        then
          let uu____13407 =
            let uu____13408 =
              let uu____13409 =
                let uu____13410 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____13410 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____13409  in
            FStar_SMTEncoding_Term.Caption uu____13408  in
          uu____13407 :: decls
        else decls  in
      (let uu____13421 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13421
       then
         let uu____13422 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____13422
       else ());
      (let env =
         let uu____13425 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____13425 tcenv  in
       let uu____13426 = encode_top_level_facts env se  in
       match uu____13426 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____13440 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____13440)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____13452 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____13452
       then
         let uu____13453 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____13453
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____13488  ->
                 fun se  ->
                   match uu____13488 with
                   | (g,env2) ->
                       let uu____13508 = encode_top_level_facts env2 se  in
                       (match uu____13508 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____13531 =
         encode_signature
           (let uu___97_13540 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___97_13540.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___97_13540.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___97_13540.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___97_13540.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___97_13540.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___97_13540.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___97_13540.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___97_13540.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___97_13540.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___97_13540.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____13531 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____13557 = FStar_Options.log_queries ()  in
             if uu____13557
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___98_13565 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___98_13565.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___98_13565.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___98_13565.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___98_13565.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___98_13565.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___98_13565.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___98_13565.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___98_13565.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___98_13565.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___98_13565.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____13567 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____13567
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
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
        (let uu____13619 =
           let uu____13620 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____13620.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____13619);
        (let env =
           let uu____13622 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____13622 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____13634 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____13669 = aux rest  in
                 (match uu____13669 with
                  | (out,rest1) ->
                      let t =
                        let uu____13699 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____13699 with
                        | FStar_Pervasives_Native.Some uu____13704 ->
                            let uu____13705 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____13705
                              x.FStar_Syntax_Syntax.sort
                        | uu____13706 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____13710 =
                        let uu____13713 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___99_13716 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___99_13716.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___99_13716.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____13713 :: out  in
                      (uu____13710, rest1))
             | uu____13721 -> ([], bindings1)  in
           let uu____13728 = aux bindings  in
           match uu____13728 with
           | (closing,bindings1) ->
               let uu____13753 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____13753, bindings1)
            in
         match uu____13634 with
         | (q1,bindings1) ->
             let uu____13776 =
               let uu____13781 =
                 FStar_List.filter
                   (fun uu___81_13786  ->
                      match uu___81_13786 with
                      | FStar_TypeChecker_Env.Binding_sig uu____13787 ->
                          false
                      | uu____13794 -> true) bindings1
                  in
               encode_env_bindings env uu____13781  in
             (match uu____13776 with
              | (env_decls,env1) ->
                  ((let uu____13812 =
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
                    if uu____13812
                    then
                      let uu____13813 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____13813
                    else ());
                   (let uu____13815 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____13815 with
                    | (phi,qdecls) ->
                        let uu____13836 =
                          let uu____13841 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____13841 phi
                           in
                        (match uu____13836 with
                         | (labels,phi1) ->
                             let uu____13858 = encode_labels labels  in
                             (match uu____13858 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____13895 =
                                      let uu____13902 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____13903 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____13902,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____13903)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13895
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
  