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
  let uu____119 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____119 with
  | (asym,a) ->
      let uu____126 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____126 with
       | (xsym,x) ->
           let uu____133 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____133 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____187 =
                      let uu____198 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____198, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____187  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____224 =
                      let uu____231 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____231)  in
                    FStar_SMTEncoding_Util.mkApp uu____224  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____244 =
                    let uu____247 =
                      let uu____250 =
                        let uu____253 =
                          let uu____254 =
                            let uu____261 =
                              let uu____262 =
                                let uu____273 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____273)  in
                              FStar_SMTEncoding_Util.mkForall uu____262  in
                            (uu____261, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____254  in
                        let uu____290 =
                          let uu____293 =
                            let uu____294 =
                              let uu____301 =
                                let uu____302 =
                                  let uu____313 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____313)  in
                                FStar_SMTEncoding_Util.mkForall uu____302  in
                              (uu____301,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____294  in
                          [uu____293]  in
                        uu____253 :: uu____290  in
                      xtok_decl :: uu____250  in
                    xname_decl :: uu____247  in
                  (xtok1, (FStar_List.length vars), uu____244)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____411 =
                    let uu____427 =
                      let uu____440 =
                        let uu____441 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____441
                         in
                      quant axy uu____440  in
                    (FStar_Parser_Const.op_Eq, uu____427)  in
                  let uu____453 =
                    let uu____471 =
                      let uu____487 =
                        let uu____500 =
                          let uu____501 =
                            let uu____502 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____502  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____501
                           in
                        quant axy uu____500  in
                      (FStar_Parser_Const.op_notEq, uu____487)  in
                    let uu____514 =
                      let uu____532 =
                        let uu____548 =
                          let uu____561 =
                            let uu____562 =
                              let uu____563 =
                                let uu____568 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____569 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____568, uu____569)  in
                              FStar_SMTEncoding_Util.mkLT uu____563  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____562
                             in
                          quant xy uu____561  in
                        (FStar_Parser_Const.op_LT, uu____548)  in
                      let uu____581 =
                        let uu____599 =
                          let uu____615 =
                            let uu____628 =
                              let uu____629 =
                                let uu____630 =
                                  let uu____635 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____636 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____635, uu____636)  in
                                FStar_SMTEncoding_Util.mkLTE uu____630  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____629
                               in
                            quant xy uu____628  in
                          (FStar_Parser_Const.op_LTE, uu____615)  in
                        let uu____648 =
                          let uu____666 =
                            let uu____682 =
                              let uu____695 =
                                let uu____696 =
                                  let uu____697 =
                                    let uu____702 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____703 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____702, uu____703)  in
                                  FStar_SMTEncoding_Util.mkGT uu____697  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____696
                                 in
                              quant xy uu____695  in
                            (FStar_Parser_Const.op_GT, uu____682)  in
                          let uu____715 =
                            let uu____733 =
                              let uu____749 =
                                let uu____762 =
                                  let uu____763 =
                                    let uu____764 =
                                      let uu____769 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____770 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____769, uu____770)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____764
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____763
                                   in
                                quant xy uu____762  in
                              (FStar_Parser_Const.op_GTE, uu____749)  in
                            let uu____782 =
                              let uu____800 =
                                let uu____816 =
                                  let uu____829 =
                                    let uu____830 =
                                      let uu____831 =
                                        let uu____836 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____837 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____836, uu____837)  in
                                      FStar_SMTEncoding_Util.mkSub uu____831
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____830
                                     in
                                  quant xy uu____829  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____816)
                                 in
                              let uu____849 =
                                let uu____867 =
                                  let uu____883 =
                                    let uu____896 =
                                      let uu____897 =
                                        let uu____898 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____898
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____897
                                       in
                                    quant qx uu____896  in
                                  (FStar_Parser_Const.op_Minus, uu____883)
                                   in
                                let uu____910 =
                                  let uu____928 =
                                    let uu____944 =
                                      let uu____957 =
                                        let uu____958 =
                                          let uu____959 =
                                            let uu____964 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____965 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____964, uu____965)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____959
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____958
                                         in
                                      quant xy uu____957  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____944)
                                     in
                                  let uu____977 =
                                    let uu____995 =
                                      let uu____1011 =
                                        let uu____1024 =
                                          let uu____1025 =
                                            let uu____1026 =
                                              let uu____1031 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1032 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1031, uu____1032)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1026
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1025
                                           in
                                        quant xy uu____1024  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1011)
                                       in
                                    let uu____1044 =
                                      let uu____1062 =
                                        let uu____1078 =
                                          let uu____1091 =
                                            let uu____1092 =
                                              let uu____1093 =
                                                let uu____1098 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1099 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1098, uu____1099)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1093
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1092
                                             in
                                          quant xy uu____1091  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1078)
                                         in
                                      let uu____1111 =
                                        let uu____1129 =
                                          let uu____1145 =
                                            let uu____1158 =
                                              let uu____1159 =
                                                let uu____1160 =
                                                  let uu____1165 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1166 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1165, uu____1166)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1160
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1159
                                               in
                                            quant xy uu____1158  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1145)
                                           in
                                        let uu____1178 =
                                          let uu____1196 =
                                            let uu____1212 =
                                              let uu____1225 =
                                                let uu____1226 =
                                                  let uu____1227 =
                                                    let uu____1232 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1233 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1232, uu____1233)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1227
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1226
                                                 in
                                              quant xy uu____1225  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1212)
                                             in
                                          let uu____1245 =
                                            let uu____1263 =
                                              let uu____1279 =
                                                let uu____1292 =
                                                  let uu____1293 =
                                                    let uu____1294 =
                                                      let uu____1299 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1300 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1299,
                                                        uu____1300)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1294
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1293
                                                   in
                                                quant xy uu____1292  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1279)
                                               in
                                            let uu____1312 =
                                              let uu____1330 =
                                                let uu____1346 =
                                                  let uu____1359 =
                                                    let uu____1360 =
                                                      let uu____1361 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1361
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1360
                                                     in
                                                  quant qx uu____1359  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1346)
                                                 in
                                              [uu____1330]  in
                                            uu____1263 :: uu____1312  in
                                          uu____1196 :: uu____1245  in
                                        uu____1129 :: uu____1178  in
                                      uu____1062 :: uu____1111  in
                                    uu____995 :: uu____1044  in
                                  uu____928 :: uu____977  in
                                uu____867 :: uu____910  in
                              uu____800 :: uu____849  in
                            uu____733 :: uu____782  in
                          uu____666 :: uu____715  in
                        uu____599 :: uu____648  in
                      uu____532 :: uu____581  in
                    uu____471 :: uu____514  in
                  uu____411 :: uu____453  in
                let mk1 l v1 =
                  let uu____1632 =
                    let uu____1643 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1713  ->
                              match uu____1713 with
                              | (l',uu____1729) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____1643
                      (FStar_Option.map
                         (fun uu____1805  ->
                            match uu____1805 with | (uu____1828,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____1632 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____1919  ->
                          match uu____1919 with
                          | (l',uu____1935) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____1985 =
          FStar_SMTEncoding_Env.fresh_fvar "x"
            FStar_SMTEncoding_Term.Term_sort
           in
        match uu____1985 with
        | (xxsym,xx) ->
            let uu____1992 =
              FStar_SMTEncoding_Env.fresh_fvar "f"
                FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____1992 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name =
                   env.FStar_SMTEncoding_Env.current_module_name  in
                 let uu____2002 =
                   let uu____2009 =
                     let uu____2010 =
                       let uu____2021 =
                         let uu____2022 =
                           let uu____2027 =
                             let uu____2028 =
                               let uu____2033 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____2033)  in
                             FStar_SMTEncoding_Util.mkEq uu____2028  in
                           (xx_has_type, uu____2027)  in
                         FStar_SMTEncoding_Util.mkImp uu____2022  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____2021)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____2010  in
                   let uu____2058 =
                     let uu____2059 =
                       let uu____2060 =
                         let uu____2061 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____2061  in
                       Prims.strcat module_name uu____2060  in
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                       uu____2059
                      in
                   (uu____2009, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____2058)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____2002)
  
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
    let uu____2111 =
      let uu____2112 =
        let uu____2119 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2119, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2112  in
    let uu____2122 =
      let uu____2125 =
        let uu____2126 =
          let uu____2133 =
            let uu____2134 =
              let uu____2145 =
                let uu____2146 =
                  let uu____2151 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2151)  in
                FStar_SMTEncoding_Util.mkImp uu____2146  in
              ([[typing_pred]], [xx], uu____2145)  in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2134  in
          (uu____2133, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2126  in
      [uu____2125]  in
    uu____2111 :: uu____2122  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2199 =
      let uu____2200 =
        let uu____2207 =
          let uu____2208 =
            let uu____2219 =
              let uu____2224 =
                let uu____2227 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2227]  in
              [uu____2224]  in
            let uu____2232 =
              let uu____2233 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2233 tt  in
            (uu____2219, [bb], uu____2232)  in
          FStar_SMTEncoding_Util.mkForall uu____2208  in
        (uu____2207, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2200  in
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
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2283)  in
                FStar_SMTEncoding_Util.mkImp uu____2278  in
              ([[typing_pred]], [xx], uu____2277)  in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2266  in
          (uu____2265, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2258  in
      [uu____2257]  in
    uu____2199 :: uu____2254  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____2339 =
        let uu____2340 =
          let uu____2347 =
            let uu____2350 =
              let uu____2353 =
                let uu____2356 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____2357 =
                  let uu____2360 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____2360]  in
                uu____2356 :: uu____2357  in
              tt :: uu____2353  in
            tt :: uu____2350  in
          ("Prims.Precedes", uu____2347)  in
        FStar_SMTEncoding_Util.mkApp uu____2340  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2339  in
    let precedes_y_x =
      let uu____2364 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2364  in
    let uu____2367 =
      let uu____2368 =
        let uu____2375 =
          let uu____2376 =
            let uu____2387 =
              let uu____2392 =
                let uu____2395 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2395]  in
              [uu____2392]  in
            let uu____2400 =
              let uu____2401 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2401 tt  in
            (uu____2387, [bb], uu____2400)  in
          FStar_SMTEncoding_Util.mkForall uu____2376  in
        (uu____2375, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2368  in
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
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2451)  in
                FStar_SMTEncoding_Util.mkImp uu____2446  in
              ([[typing_pred]], [xx], uu____2445)  in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2434  in
          (uu____2433, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2426  in
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
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2522 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2521, uu____2522)  in
                              FStar_SMTEncoding_Util.mkGT uu____2516  in
                            let uu____2523 =
                              let uu____2526 =
                                let uu____2527 =
                                  let uu____2532 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2533 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2532, uu____2533)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2527  in
                              let uu____2534 =
                                let uu____2537 =
                                  let uu____2538 =
                                    let uu____2543 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2544 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2543, uu____2544)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2538  in
                                [uu____2537]  in
                              uu____2526 :: uu____2534  in
                            uu____2515 :: uu____2523  in
                          typing_pred_y :: uu____2512  in
                        typing_pred :: uu____2509  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2506  in
                    (uu____2505, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2500  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2499)
                 in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2488  in
            (uu____2487,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2480  in
        [uu____2479]  in
      uu____2425 :: uu____2476  in
    uu____2367 :: uu____2422  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2596 =
      let uu____2597 =
        let uu____2604 =
          let uu____2605 =
            let uu____2616 =
              let uu____2621 =
                let uu____2624 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2624]  in
              [uu____2621]  in
            let uu____2629 =
              let uu____2630 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2630 tt  in
            (uu____2616, [bb], uu____2629)  in
          FStar_SMTEncoding_Util.mkForall uu____2605  in
        (uu____2604, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2597  in
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
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____2680)  in
                FStar_SMTEncoding_Util.mkImp uu____2675  in
              ([[typing_pred]], [xx], uu____2674)  in
            FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2663  in
          (uu____2662, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2655  in
      [uu____2654]  in
    uu____2596 :: uu____2651  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____2745 =
      let uu____2746 =
        let uu____2753 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____2753, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2746  in
    [uu____2745]  in
  let mk_and_interp env conj uu____2771 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____2796 =
      let uu____2797 =
        let uu____2804 =
          let uu____2805 =
            let uu____2816 =
              let uu____2817 =
                let uu____2822 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____2822, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____2817  in
            ([[l_and_a_b]], [aa; bb], uu____2816)  in
          FStar_SMTEncoding_Util.mkForall uu____2805  in
        (uu____2804, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2797  in
    [uu____2796]  in
  let mk_or_interp env disj uu____2866 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____2891 =
      let uu____2892 =
        let uu____2899 =
          let uu____2900 =
            let uu____2911 =
              let uu____2912 =
                let uu____2917 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____2917, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____2912  in
            ([[l_or_a_b]], [aa; bb], uu____2911)  in
          FStar_SMTEncoding_Util.mkForall uu____2900  in
        (uu____2899, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2892  in
    [uu____2891]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____2986 =
      let uu____2987 =
        let uu____2994 =
          let uu____2995 =
            let uu____3006 =
              let uu____3007 =
                let uu____3012 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3012, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3007  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3006)  in
          FStar_SMTEncoding_Util.mkForall uu____2995  in
        (uu____2994, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2987  in
    [uu____2986]  in
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
    let uu____3091 =
      let uu____3092 =
        let uu____3099 =
          let uu____3100 =
            let uu____3111 =
              let uu____3112 =
                let uu____3117 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3117, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3112  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3111)  in
          FStar_SMTEncoding_Util.mkForall uu____3100  in
        (uu____3099, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3092  in
    [uu____3091]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3194 =
      let uu____3195 =
        let uu____3202 =
          let uu____3203 =
            let uu____3214 =
              let uu____3215 =
                let uu____3220 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3220, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3215  in
            ([[l_imp_a_b]], [aa; bb], uu____3214)  in
          FStar_SMTEncoding_Util.mkForall uu____3203  in
        (uu____3202, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3195  in
    [uu____3194]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3289 =
      let uu____3290 =
        let uu____3297 =
          let uu____3298 =
            let uu____3309 =
              let uu____3310 =
                let uu____3315 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3315, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3310  in
            ([[l_iff_a_b]], [aa; bb], uu____3309)  in
          FStar_SMTEncoding_Util.mkForall uu____3298  in
        (uu____3297, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3290  in
    [uu____3289]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3373 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3373  in
    let uu____3376 =
      let uu____3377 =
        let uu____3384 =
          let uu____3385 =
            let uu____3396 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3396)  in
          FStar_SMTEncoding_Util.mkForall uu____3385  in
        (uu____3384, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3377  in
    [uu____3376]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____3462 =
        let uu____3469 =
          let uu____3472 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____3472]  in
        ("Valid", uu____3469)  in
      FStar_SMTEncoding_Util.mkApp uu____3462  in
    let uu____3475 =
      let uu____3476 =
        let uu____3483 =
          let uu____3484 =
            let uu____3495 =
              let uu____3496 =
                let uu____3501 =
                  let uu____3502 =
                    let uu____3513 =
                      let uu____3518 =
                        let uu____3521 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____3521]  in
                      [uu____3518]  in
                    let uu____3526 =
                      let uu____3527 =
                        let uu____3532 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____3532, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____3527  in
                    (uu____3513, [xx1], uu____3526)  in
                  FStar_SMTEncoding_Util.mkForall uu____3502  in
                (uu____3501, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3496  in
            ([[l_forall_a_b]], [aa; bb], uu____3495)  in
          FStar_SMTEncoding_Util.mkForall uu____3484  in
        (uu____3483, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3476  in
    [uu____3475]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____3620 =
        let uu____3627 =
          let uu____3630 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____3630]  in
        ("Valid", uu____3627)  in
      FStar_SMTEncoding_Util.mkApp uu____3620  in
    let uu____3633 =
      let uu____3634 =
        let uu____3641 =
          let uu____3642 =
            let uu____3653 =
              let uu____3654 =
                let uu____3659 =
                  let uu____3660 =
                    let uu____3671 =
                      let uu____3676 =
                        let uu____3679 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____3679]  in
                      [uu____3676]  in
                    let uu____3684 =
                      let uu____3685 =
                        let uu____3690 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____3690, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____3685  in
                    (uu____3671, [xx1], uu____3684)  in
                  FStar_SMTEncoding_Util.mkExists uu____3660  in
                (uu____3659, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3654  in
            ([[l_exists_a_b]], [aa; bb], uu____3653)  in
          FStar_SMTEncoding_Util.mkForall uu____3642  in
        (uu____3641, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3634  in
    [uu____3633]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3756 =
      let uu____3757 =
        let uu____3764 =
          let uu____3765 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3765 range_ty  in
        let uu____3766 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3764, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3766)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3757  in
    [uu____3756]  in
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
        let uu____3806 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3806 x1 t  in
      let uu____3807 =
        let uu____3818 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3818)  in
      FStar_SMTEncoding_Util.mkForall uu____3807  in
    let uu____3841 =
      let uu____3842 =
        let uu____3849 =
          let uu____3850 =
            let uu____3861 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3861)  in
          FStar_SMTEncoding_Util.mkForall uu____3850  in
        (uu____3849,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3842  in
    [uu____3841]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3917 =
      let uu____3918 =
        let uu____3925 =
          let uu____3926 =
            let uu____3941 =
              let uu____3942 =
                let uu____3947 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3948 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3947, uu____3948)  in
              FStar_SMTEncoding_Util.mkAnd uu____3942  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3941)
             in
          FStar_SMTEncoding_Util.mkForall' uu____3926  in
        (uu____3925,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3918  in
    [uu____3917]  in
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
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____4408 =
            FStar_Util.find_opt
              (fun uu____4440  ->
                 match uu____4440 with
                 | (l,uu____4452) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4408 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4486,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4537 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4537 with
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
              let uu____4589 =
                ((let uu____4592 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4592) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4589
              then
                let arg_sorts =
                  let uu____4602 =
                    let uu____4603 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4603.FStar_Syntax_Syntax.n  in
                  match uu____4602 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4609) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4639  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4644 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4646 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4646 with
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
                (let uu____4679 = prims.is lid  in
                 if uu____4679
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4687 = prims.mk lid vname  in
                   match uu____4687 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4714 =
                      let uu____4725 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4725 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4743 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4743
                            then
                              let uu____4744 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___87_4747 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___87_4747.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___87_4747.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___87_4747.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___87_4747.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___87_4747.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___87_4747.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___87_4747.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___87_4747.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___87_4747.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___87_4747.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___87_4747.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___87_4747.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___87_4747.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___87_4747.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___87_4747.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___87_4747.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___87_4747.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___87_4747.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___87_4747.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___87_4747.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___87_4747.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___87_4747.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___87_4747.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___87_4747.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___87_4747.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___87_4747.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___87_4747.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___87_4747.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___87_4747.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___87_4747.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___87_4747.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___87_4747.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___87_4747.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___87_4747.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___87_4747.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___87_4747.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4744
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4759 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4759)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4714 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4809 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4809 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4834 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___76_4884  ->
                                       match uu___76_4884 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4888 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4888 with
                                            | (uu____4909,(xxsym,uu____4911))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4929 =
                                                  let uu____4930 =
                                                    let uu____4937 =
                                                      let uu____4938 =
                                                        let uu____4949 =
                                                          let uu____4950 =
                                                            let uu____4955 =
                                                              let uu____4956
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4956
                                                               in
                                                            (vapp,
                                                              uu____4955)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4950
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4949)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4938
                                                       in
                                                    (uu____4937,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4930
                                                   in
                                                [uu____4929])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4975 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4975 with
                                            | (uu____4996,(xxsym,uu____4998))
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
                                                let uu____5021 =
                                                  let uu____5022 =
                                                    let uu____5029 =
                                                      let uu____5030 =
                                                        let uu____5041 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5041)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5030
                                                       in
                                                    (uu____5029,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5022
                                                   in
                                                [uu____5021])
                                       | uu____5058 -> []))
                                in
                             let uu____5059 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5059 with
                              | (vars,guards,env',decls1,uu____5086) ->
                                  let uu____5099 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5108 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5108, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5110 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5110 with
                                         | (g,ds) ->
                                             let uu____5121 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5121,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5099 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5134 =
                                           let uu____5141 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5141)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5134
                                          in
                                       let uu____5150 =
                                         let vname_decl =
                                           let uu____5158 =
                                             let uu____5169 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5179  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5169,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5158
                                            in
                                         let uu____5188 =
                                           let env2 =
                                             let uu___88_5194 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bindings
                                                 =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___88_5194.FStar_SMTEncoding_Env.current_module_name)
                                             }  in
                                           let uu____5195 =
                                             let uu____5196 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5196  in
                                           if uu____5195
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5188 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____5211::uu____5212 ->
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
                                                     let uu____5252 =
                                                       let uu____5263 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____5263)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____5252
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____5290 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____5293 =
                                               match formals with
                                               | [] ->
                                                   let uu____5310 =
                                                     let uu____5311 =
                                                       let uu____5314 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_18  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_18)
                                                         uu____5314
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____5311
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____5310)
                                               | uu____5323 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5330 =
                                                       let uu____5337 =
                                                         let uu____5338 =
                                                           let uu____5349 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____5349)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____5338
                                                          in
                                                       (uu____5337,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5330
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____5293 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5150 with
                                        | (decls2,env2) ->
                                            let uu____5392 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5400 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5400 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5413 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5413,
                                                    decls)
                                               in
                                            (match uu____5392 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5424 =
                                                     let uu____5431 =
                                                       let uu____5432 =
                                                         let uu____5443 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5443)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____5432
                                                        in
                                                     (uu____5431,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5424
                                                    in
                                                 let freshness =
                                                   let uu____5459 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5459
                                                   then
                                                     let uu____5464 =
                                                       let uu____5465 =
                                                         let uu____5476 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5487 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5476,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5487)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5465
                                                        in
                                                     let uu____5490 =
                                                       let uu____5493 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____5493]  in
                                                     uu____5464 :: uu____5490
                                                   else []  in
                                                 let g =
                                                   let uu____5498 =
                                                     let uu____5501 =
                                                       let uu____5504 =
                                                         let uu____5507 =
                                                           let uu____5510 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5510
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5507
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5504
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5501
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5498
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
          let uu____5543 =
            FStar_SMTEncoding_Env.try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5543 with
          | FStar_Pervasives_Native.None  ->
              let uu____5554 = encode_free_var false env x t t_norm []  in
              (match uu____5554 with
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
            let uu____5617 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5617 with
            | (decls,env1) ->
                let uu____5636 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5636
                then
                  let uu____5643 =
                    let uu____5646 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5646  in
                  (uu____5643, env1)
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
             (fun uu____5704  ->
                fun lb  ->
                  match uu____5704 with
                  | (decls,env1) ->
                      let uu____5724 =
                        let uu____5731 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5731
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5724 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5754 = FStar_Syntax_Util.head_and_args t  in
    match uu____5754 with
    | (hd1,args) ->
        let uu____5791 =
          let uu____5792 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5792.FStar_Syntax_Syntax.n  in
        (match uu____5791 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5796,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5815 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5821 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5849  ->
      fun quals  ->
        match uu____5849 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5933 = FStar_Util.first_N nbinders formals  in
              match uu____5933 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6014  ->
                         fun uu____6015  ->
                           match (uu____6014, uu____6015) with
                           | ((formal,uu____6033),(binder,uu____6035)) ->
                               let uu____6044 =
                                 let uu____6051 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6051)  in
                               FStar_Syntax_Syntax.NT uu____6044) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6059 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6090  ->
                              match uu____6090 with
                              | (x,i) ->
                                  let uu____6101 =
                                    let uu___89_6102 = x  in
                                    let uu____6103 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___89_6102.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___89_6102.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6103
                                    }  in
                                  (uu____6101, i)))
                       in
                    FStar_All.pipe_right uu____6059
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6121 =
                      let uu____6126 = FStar_Syntax_Subst.compress body  in
                      let uu____6127 =
                        let uu____6128 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6128
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6126 uu____6127
                       in
                    uu____6121 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6197 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6197
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___90_6200 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___90_6200.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___90_6200.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___90_6200.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___90_6200.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___90_6200.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___90_6200.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___90_6200.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___90_6200.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___90_6200.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___90_6200.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___90_6200.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___90_6200.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___90_6200.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___90_6200.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___90_6200.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___90_6200.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___90_6200.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___90_6200.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___90_6200.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___90_6200.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___90_6200.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___90_6200.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___90_6200.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___90_6200.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___90_6200.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___90_6200.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___90_6200.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___90_6200.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___90_6200.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___90_6200.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___90_6200.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___90_6200.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___90_6200.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___90_6200.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___90_6200.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___90_6200.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6237 = FStar_Syntax_Util.abs_formals e  in
                match uu____6237 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6301::uu____6302 ->
                         let uu____6317 =
                           let uu____6318 =
                             let uu____6321 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6321
                              in
                           uu____6318.FStar_Syntax_Syntax.n  in
                         (match uu____6317 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6364 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6364 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6406 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6406
                                   then
                                     let uu____6441 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6441 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6535  ->
                                                   fun uu____6536  ->
                                                     match (uu____6535,
                                                             uu____6536)
                                                     with
                                                     | ((x,uu____6554),
                                                        (b,uu____6556)) ->
                                                         let uu____6565 =
                                                           let uu____6572 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6572)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6565)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6574 =
                                            let uu____6595 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6595)  in
                                          (uu____6574, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6663 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6663 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6752) ->
                              let uu____6757 =
                                let uu____6778 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6778  in
                              (uu____6757, true)
                          | uu____6843 when Prims.op_Negation norm1 ->
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
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____6845 ->
                              let uu____6846 =
                                let uu____6847 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____6848 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____6847 uu____6848
                                 in
                              failwith uu____6846)
                     | uu____6873 ->
                         let rec aux' t_norm2 =
                           let uu____6900 =
                             let uu____6901 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____6901.FStar_Syntax_Syntax.n  in
                           match uu____6900 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____6942 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____6942 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____6970 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____6970 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7050) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7055 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____7111 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____7111
               then encode_top_level_vals env bindings quals
               else
                 (let uu____7123 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____7186  ->
                            fun lb  ->
                              match uu____7186 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____7241 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____7241
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____7244 =
                                      let uu____7253 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____7253
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____7244 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____7123 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7378 =
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
                        | uu____7384 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7392 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7392 vars)
                            else
                              (let uu____7394 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7394)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7454;
                             FStar_Syntax_Syntax.lbeff = uu____7455;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7457;
                             FStar_Syntax_Syntax.lbpos = uu____7458;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7482 =
                              let uu____7489 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7489 with
                              | (tcenv',uu____7507,e_t) ->
                                  let uu____7513 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7524 -> failwith "Impossible"  in
                                  (match uu____7513 with
                                   | (e1,t_norm1) ->
                                       ((let uu___93_7540 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bindings =
                                             (uu___93_7540.FStar_SMTEncoding_Env.bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___93_7540.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___93_7540.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___93_7540.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___93_7540.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___93_7540.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___93_7540.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___93_7540.FStar_SMTEncoding_Env.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____7482 with
                             | (env',e1,t_norm1) ->
                                 let uu____7550 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7550 with
                                  | ((binders,body,uu____7571,t_body),curry)
                                      ->
                                      ((let uu____7583 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7583
                                        then
                                          let uu____7584 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7585 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7584 uu____7585
                                        else ());
                                       (let uu____7587 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7587 with
                                        | (vars,guards,env'1,binder_decls,uu____7614)
                                            ->
                                            let body1 =
                                              let uu____7628 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7628
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
                                              let uu____7645 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7645 curry fvb
                                                vars
                                               in
                                            let uu____7646 =
                                              let uu____7655 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7655
                                              then
                                                let uu____7666 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7667 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7666, uu____7667)
                                              else
                                                (let uu____7677 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7677))
                                               in
                                            (match uu____7646 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7700 =
                                                     let uu____7707 =
                                                       let uu____7708 =
                                                         let uu____7719 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7719)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____7708
                                                        in
                                                     let uu____7730 =
                                                       let uu____7733 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7733
                                                        in
                                                     (uu____7707, uu____7730,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7700
                                                    in
                                                 let uu____7736 =
                                                   let uu____7739 =
                                                     let uu____7742 =
                                                       let uu____7745 =
                                                         let uu____7748 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7748
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7745
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7742
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7739
                                                    in
                                                 (uu____7736, env2))))))
                        | uu____7753 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____7816 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____7816, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____7819 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____7866  ->
                                  fun fvb  ->
                                    match uu____7866 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____7912 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7912
                                           in
                                        let gtok =
                                          let uu____7914 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____7914
                                           in
                                        let env4 =
                                          let uu____7916 =
                                            let uu____7919 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_19  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_19) uu____7919
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____7916
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____7819 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____8027 t_norm
                              uu____8029 =
                              match (uu____8027, uu____8029) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____8059;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____8060;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____8062;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____8063;_})
                                  ->
                                  let uu____8084 =
                                    let uu____8091 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____8091 with
                                    | (tcenv',uu____8113,e_t) ->
                                        let uu____8119 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____8130 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____8119 with
                                         | (e1,t_norm1) ->
                                             ((let uu___94_8146 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bindings
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___94_8146.FStar_SMTEncoding_Env.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____8084 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____8161 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____8161
                                         then
                                           let uu____8162 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____8163 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____8164 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____8162 uu____8163 uu____8164
                                         else ());
                                        (let uu____8166 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____8166 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____8203 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8203
                                               then
                                                 let uu____8204 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8205 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8206 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____8207 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____8204 uu____8205
                                                   uu____8206 uu____8207
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____8211 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8211 with
                                               | (vars,guards,env'1,binder_decls,uu____8242)
                                                   ->
                                                   let decl_g =
                                                     let uu____8256 =
                                                       let uu____8267 =
                                                         let uu____8270 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____8270
                                                          in
                                                       (g, uu____8267,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____8256
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
                                                     let uu____8295 =
                                                       let uu____8302 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____8302)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8295
                                                      in
                                                   let gsapp =
                                                     let uu____8312 =
                                                       let uu____8319 =
                                                         let uu____8322 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____8322 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8319)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8312
                                                      in
                                                   let gmax =
                                                     let uu____8328 =
                                                       let uu____8335 =
                                                         let uu____8338 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____8338 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8335)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8328
                                                      in
                                                   let body1 =
                                                     let uu____8344 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8344
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____8346 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____8346 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8364 =
                                                            let uu____8371 =
                                                              let uu____8372
                                                                =
                                                                let uu____8387
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
                                                                  uu____8387)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____8372
                                                               in
                                                            let uu____8408 =
                                                              let uu____8411
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8411
                                                               in
                                                            (uu____8371,
                                                              uu____8408,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8364
                                                           in
                                                        let eqn_f =
                                                          let uu____8415 =
                                                            let uu____8422 =
                                                              let uu____8423
                                                                =
                                                                let uu____8434
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8434)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____8423
                                                               in
                                                            (uu____8422,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8415
                                                           in
                                                        let eqn_g' =
                                                          let uu____8448 =
                                                            let uu____8455 =
                                                              let uu____8456
                                                                =
                                                                let uu____8467
                                                                  =
                                                                  let uu____8468
                                                                    =
                                                                    let uu____8473
                                                                    =
                                                                    let uu____8474
                                                                    =
                                                                    let uu____8481
                                                                    =
                                                                    let uu____8484
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8484
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8481)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8474
                                                                     in
                                                                    (gsapp,
                                                                    uu____8473)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8468
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8467)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____8456
                                                               in
                                                            (uu____8455,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8448
                                                           in
                                                        let uu____8507 =
                                                          let uu____8516 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8516
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8545)
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
                                                                  let uu____8570
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8570
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8575
                                                                  =
                                                                  let uu____8582
                                                                    =
                                                                    let uu____8583
                                                                    =
                                                                    let uu____8594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8594)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____8583
                                                                     in
                                                                  (uu____8582,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8575
                                                                 in
                                                              let uu____8615
                                                                =
                                                                let uu____8622
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8622
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8635
                                                                    =
                                                                    let uu____8638
                                                                    =
                                                                    let uu____8639
                                                                    =
                                                                    let uu____8646
                                                                    =
                                                                    let uu____8647
                                                                    =
                                                                    let uu____8658
                                                                    =
                                                                    let uu____8659
                                                                    =
                                                                    let uu____8664
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8664,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8659
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8658)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____8647
                                                                     in
                                                                    (uu____8646,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8639
                                                                     in
                                                                    [uu____8638]
                                                                     in
                                                                    (d3,
                                                                    uu____8635)
                                                                 in
                                                              (match uu____8615
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
                                                        (match uu____8507
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
                            let uu____8729 =
                              let uu____8742 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8803  ->
                                   fun uu____8804  ->
                                     match (uu____8803, uu____8804) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____8929 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____8929 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8742
                               in
                            (match uu____8729 with
                             | (decls2,eqns,env01) ->
                                 let uu____9002 =
                                   let isDeclFun uu___77_9016 =
                                     match uu___77_9016 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____9017 -> true
                                     | uu____9028 -> false  in
                                   let uu____9029 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____9029
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____9002 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____9069 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___78_9073  ->
                                 match uu___78_9073 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9074 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____9080 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____9080)))
                         in
                      if uu____9069
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
                   let uu____9132 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9132
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
        let uu____9193 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9193 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9197 = encode_sigelt' env se  in
      match uu____9197 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9213 =
                  let uu____9214 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9214  in
                [uu____9213]
            | uu____9215 ->
                let uu____9216 =
                  let uu____9219 =
                    let uu____9220 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9220  in
                  uu____9219 :: g  in
                let uu____9221 =
                  let uu____9224 =
                    let uu____9225 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9225  in
                  [uu____9224]  in
                FStar_List.append uu____9216 uu____9221
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
        let uu____9240 =
          let uu____9241 = FStar_Syntax_Subst.compress t  in
          uu____9241.FStar_Syntax_Syntax.n  in
        match uu____9240 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9245)) -> s = "opaque_to_smt"
        | uu____9246 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9253 =
          let uu____9254 = FStar_Syntax_Subst.compress t  in
          uu____9254.FStar_Syntax_Syntax.n  in
        match uu____9253 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9258)) -> s = "uninterpreted_by_smt"
        | uu____9259 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9264 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9269 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9280 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9283 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9286 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9301 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9305 =
            let uu____9306 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____9306 Prims.op_Negation  in
          if uu____9305
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9334 ->
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
               let uu____9358 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9358 with
               | (formals,uu____9376) ->
                   let arity = FStar_List.length formals  in
                   let uu____9394 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9394 with
                    | (aname,atok,env2) ->
                        let uu____9414 =
                          let uu____9419 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9419
                            env2
                           in
                        (match uu____9414 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9431 =
                                 let uu____9432 =
                                   let uu____9443 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9459  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9443,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9432
                                  in
                               [uu____9431;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9472 =
                               let aux uu____9528 uu____9529 =
                                 match (uu____9528, uu____9529) with
                                 | ((bv,uu____9581),(env3,acc_sorts,acc)) ->
                                     let uu____9619 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9619 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9472 with
                              | (uu____9691,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9714 =
                                      let uu____9721 =
                                        let uu____9722 =
                                          let uu____9733 =
                                            let uu____9734 =
                                              let uu____9739 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9739)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9734
                                             in
                                          ([[app]], xs_sorts, uu____9733)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____9722
                                         in
                                      (uu____9721,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9714
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
                                    let uu____9759 =
                                      let uu____9766 =
                                        let uu____9767 =
                                          let uu____9778 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9778)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____9767
                                         in
                                      (uu____9766,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9759
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9797 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9797 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9825,uu____9826) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9827 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9827 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9844,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9850 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___79_9854  ->
                      match uu___79_9854 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9855 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____9860 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9861 -> false))
               in
            Prims.op_Negation uu____9850  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____9870 =
               let uu____9877 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____9877 env fv t quals  in
             match uu____9870 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____9892 =
                   let uu____9895 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____9895  in
                 (uu____9892, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____9903 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____9903 with
           | (uu____9912,f1) ->
               let uu____9914 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f1 env  in
               (match uu____9914 with
                | (f2,decls) ->
                    let g =
                      let uu____9928 =
                        let uu____9929 =
                          let uu____9936 =
                            let uu____9939 =
                              let uu____9940 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____9940
                               in
                            FStar_Pervasives_Native.Some uu____9939  in
                          let uu____9941 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____9936, uu____9941)  in
                        FStar_SMTEncoding_Util.mkAssume uu____9929  in
                      [uu____9928]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____9947) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____9959 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____9977 =
                       let uu____9980 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____9980.FStar_Syntax_Syntax.fv_name  in
                     uu____9977.FStar_Syntax_Syntax.v  in
                   let uu____9981 =
                     let uu____9982 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____9982  in
                   if uu____9981
                   then
                     let val_decl =
                       let uu___97_10010 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___97_10010.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___97_10010.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___97_10010.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10015 = encode_sigelt' env1 val_decl  in
                     match uu____10015 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____9959 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10043,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10045;
                          FStar_Syntax_Syntax.lbtyp = uu____10046;
                          FStar_Syntax_Syntax.lbeff = uu____10047;
                          FStar_Syntax_Syntax.lbdef = uu____10048;
                          FStar_Syntax_Syntax.lbattrs = uu____10049;
                          FStar_Syntax_Syntax.lbpos = uu____10050;_}::[]),uu____10051)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10074 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10074 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10103 =
                   let uu____10106 =
                     let uu____10107 =
                       let uu____10114 =
                         let uu____10115 =
                           let uu____10126 =
                             let uu____10127 =
                               let uu____10132 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10132)  in
                             FStar_SMTEncoding_Util.mkEq uu____10127  in
                           ([[b2t_x]], [xx], uu____10126)  in
                         FStar_SMTEncoding_Util.mkForall uu____10115  in
                       (uu____10114,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10107  in
                   [uu____10106]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10103
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10165,uu____10166) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___80_10175  ->
                  match uu___80_10175 with
                  | FStar_Syntax_Syntax.Discriminator uu____10176 -> true
                  | uu____10177 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10180,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10191 =
                     let uu____10192 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10192.FStar_Ident.idText  in
                   uu____10191 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___81_10196  ->
                     match uu___81_10196 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10197 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10201) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___82_10218  ->
                  match uu___82_10218 with
                  | FStar_Syntax_Syntax.Projector uu____10219 -> true
                  | uu____10224 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10227 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10227 with
           | FStar_Pervasives_Native.Some uu____10234 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___98_10238 = se  in
                 let uu____10239 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10239;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___98_10238.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___98_10238.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___98_10238.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10246) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10264) ->
          let uu____10273 = encode_sigelts env ses  in
          (match uu____10273 with
           | (g,env1) ->
               let uu____10290 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___83_10313  ->
                         match uu___83_10313 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10314;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10315;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10316;_}
                             -> false
                         | uu____10319 -> true))
                  in
               (match uu____10290 with
                | (g',inversions) ->
                    let uu____10334 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___84_10355  ->
                              match uu___84_10355 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10356 ->
                                  true
                              | uu____10367 -> false))
                       in
                    (match uu____10334 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10385,tps,k,uu____10388,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___85_10405  ->
                    match uu___85_10405 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10406 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10417 = c  in
              match uu____10417 with
              | (name,args,uu____10422,uu____10423,uu____10424) ->
                  let uu____10429 =
                    let uu____10430 =
                      let uu____10441 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10458  ->
                                match uu____10458 with
                                | (uu____10465,sort,uu____10467) -> sort))
                         in
                      (name, uu____10441, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10430  in
                  [uu____10429]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____10498 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10504 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10504 FStar_Option.isNone))
               in
            if uu____10498
            then []
            else
              (let uu____10536 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10536 with
               | (xxsym,xx) ->
                   let uu____10545 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10584  ->
                             fun l  ->
                               match uu____10584 with
                               | (out,decls) ->
                                   let uu____10604 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10604 with
                                    | (uu____10615,data_t) ->
                                        let uu____10617 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10617 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10663 =
                                                 let uu____10664 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10664.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10663 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10675,indices) ->
                                                   indices
                                               | uu____10697 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10721  ->
                                                         match uu____10721
                                                         with
                                                         | (x,uu____10727) ->
                                                             let uu____10728
                                                               =
                                                               let uu____10729
                                                                 =
                                                                 let uu____10736
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10736,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10729
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10728)
                                                    env)
                                                in
                                             let uu____10739 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10739 with
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
                                                      let uu____10765 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10781
                                                                 =
                                                                 let uu____10786
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10786,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10781)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10765
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10789 =
                                                      let uu____10790 =
                                                        let uu____10795 =
                                                          let uu____10796 =
                                                            let uu____10801 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10801,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10796
                                                           in
                                                        (out, uu____10795)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10790
                                                       in
                                                    (uu____10789,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10545 with
                    | (data_ax,decls) ->
                        let uu____10814 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10814 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10825 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10825 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10829 =
                                 let uu____10836 =
                                   let uu____10837 =
                                     let uu____10848 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10863 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10848,
                                       uu____10863)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____10837
                                    in
                                 let uu____10878 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10836,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10878)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10829
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10881 =
            let uu____10894 =
              let uu____10895 = FStar_Syntax_Subst.compress k  in
              uu____10895.FStar_Syntax_Syntax.n  in
            match uu____10894 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10940 -> (tps, k)  in
          (match uu____10881 with
           | (formals,res) ->
               let uu____10963 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____10963 with
                | (formals1,res1) ->
                    let uu____10974 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____10974 with
                     | (vars,guards,env',binder_decls,uu____10999) ->
                         let arity = FStar_List.length vars  in
                         let uu____11013 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11013 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11036 =
                                  let uu____11043 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11043)  in
                                FStar_SMTEncoding_Util.mkApp uu____11036  in
                              let uu____11052 =
                                let tname_decl =
                                  let uu____11062 =
                                    let uu____11063 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11095  ->
                                              match uu____11095 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11108 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11063,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11108, false)
                                     in
                                  constructor_or_logic_type_decl uu____11062
                                   in
                                let uu____11117 =
                                  match vars with
                                  | [] ->
                                      let uu____11130 =
                                        let uu____11131 =
                                          let uu____11134 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_20  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_20) uu____11134
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11131
                                         in
                                      ([], uu____11130)
                                  | uu____11145 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11154 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11154
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11168 =
                                          let uu____11175 =
                                            let uu____11176 =
                                              let uu____11191 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11191)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____11176
                                             in
                                          (uu____11175,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11168
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11117 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____11052 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11231 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11231 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11249 =
                                               let uu____11250 =
                                                 let uu____11257 =
                                                   let uu____11258 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11258
                                                    in
                                                 (uu____11257,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11250
                                                in
                                             [uu____11249]
                                           else []  in
                                         let uu____11262 =
                                           let uu____11265 =
                                             let uu____11268 =
                                               let uu____11269 =
                                                 let uu____11276 =
                                                   let uu____11277 =
                                                     let uu____11288 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11288)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11277
                                                    in
                                                 (uu____11276,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11269
                                                in
                                             [uu____11268]  in
                                           FStar_List.append karr uu____11265
                                            in
                                         FStar_List.append decls1 uu____11262
                                      in
                                   let aux =
                                     let uu____11304 =
                                       let uu____11307 =
                                         inversion_axioms tapp vars  in
                                       let uu____11310 =
                                         let uu____11313 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____11313]  in
                                       FStar_List.append uu____11307
                                         uu____11310
                                        in
                                     FStar_List.append kindingAx uu____11304
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11320,uu____11321,uu____11322,uu____11323,uu____11324)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11332,t,uu____11334,n_tps,uu____11336) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11344 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11344 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11384 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11384 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11405 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11405 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11419 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11419 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11489 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11489,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11491 =
                                  let uu____11510 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11510, true)
                                   in
                                FStar_All.pipe_right uu____11491
                                  FStar_SMTEncoding_Term.constructor_to_decl
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
                              let uu____11549 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11549 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11561::uu____11562 ->
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
                                         let uu____11607 =
                                           let uu____11618 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11618)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____11607
                                     | uu____11643 -> tok_typing  in
                                   let uu____11652 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11652 with
                                    | (vars',guards',env'',decls_formals,uu____11677)
                                        ->
                                        let uu____11690 =
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
                                        (match uu____11690 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11721 ->
                                                   let uu____11728 =
                                                     let uu____11729 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11729
                                                      in
                                                   [uu____11728]
                                                in
                                             let encode_elim uu____11741 =
                                               let uu____11742 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11742 with
                                               | (head1,args) ->
                                                   let uu____11785 =
                                                     let uu____11786 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11786.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11785 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11796;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11797;_},uu____11798)
                                                        ->
                                                        let uu____11803 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11803
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11816
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11816
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
                                                                    uu____11865
                                                                    ->
                                                                    let uu____11866
                                                                    =
                                                                    let uu____11871
                                                                    =
                                                                    let uu____11872
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11872
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11871)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11866
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11888
                                                                    =
                                                                    let uu____11889
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11889
                                                                     in
                                                                    if
                                                                    uu____11888
                                                                    then
                                                                    let uu____11902
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11902]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11904
                                                                    =
                                                                    let uu____11917
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11967
                                                                     ->
                                                                    fun
                                                                    uu____11968
                                                                     ->
                                                                    match 
                                                                    (uu____11967,
                                                                    uu____11968)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12063
                                                                    =
                                                                    let uu____12070
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12070
                                                                     in
                                                                    (match uu____12063
                                                                    with
                                                                    | 
                                                                    (uu____12083,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12091
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12091
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12093
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12093
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
                                                                    uu____11917
                                                                     in
                                                                  (match uu____11904
                                                                   with
                                                                   | 
                                                                   (uu____12108,arg_vars,elim_eqns_or_guards,uu____12111)
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
                                                                    let uu____12139
                                                                    =
                                                                    let uu____12146
                                                                    =
                                                                    let uu____12147
                                                                    =
                                                                    let uu____12158
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12169
                                                                    =
                                                                    let uu____12170
                                                                    =
                                                                    let uu____12175
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12175)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12170
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12158,
                                                                    uu____12169)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12147
                                                                     in
                                                                    (uu____12146,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12139
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12193
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12193
                                                                    then
                                                                    let x =
                                                                    let uu____12199
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12199,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12201
                                                                    =
                                                                    let uu____12208
                                                                    =
                                                                    let uu____12209
                                                                    =
                                                                    let uu____12220
                                                                    =
                                                                    let uu____12225
                                                                    =
                                                                    let uu____12228
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12228]
                                                                     in
                                                                    [uu____12225]
                                                                     in
                                                                    let uu____12233
                                                                    =
                                                                    let uu____12234
                                                                    =
                                                                    let uu____12239
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12239,
                                                                    uu____12240)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12234
                                                                     in
                                                                    (uu____12220,
                                                                    [x],
                                                                    uu____12233)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12209
                                                                     in
                                                                    let uu____12259
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12208,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12259)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12201
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12266
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
                                                                    (let uu____12294
                                                                    =
                                                                    let uu____12295
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12295
                                                                    dapp1  in
                                                                    [uu____12294])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12266
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12302
                                                                    =
                                                                    let uu____12309
                                                                    =
                                                                    let uu____12310
                                                                    =
                                                                    let uu____12321
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12332
                                                                    =
                                                                    let uu____12333
                                                                    =
                                                                    let uu____12338
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12338)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12333
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12321,
                                                                    uu____12332)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12310
                                                                     in
                                                                    (uu____12309,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12302)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12358 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12358
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12371
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12371
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
                                                                    uu____12420
                                                                    ->
                                                                    let uu____12421
                                                                    =
                                                                    let uu____12426
                                                                    =
                                                                    let uu____12427
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12427
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12426)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12421
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12443
                                                                    =
                                                                    let uu____12444
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12444
                                                                     in
                                                                    if
                                                                    uu____12443
                                                                    then
                                                                    let uu____12457
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12457]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12459
                                                                    =
                                                                    let uu____12472
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12522
                                                                     ->
                                                                    fun
                                                                    uu____12523
                                                                     ->
                                                                    match 
                                                                    (uu____12522,
                                                                    uu____12523)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12618
                                                                    =
                                                                    let uu____12625
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12625
                                                                     in
                                                                    (match uu____12618
                                                                    with
                                                                    | 
                                                                    (uu____12638,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12646
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12646
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12648
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12648
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
                                                                    uu____12472
                                                                     in
                                                                  (match uu____12459
                                                                   with
                                                                   | 
                                                                   (uu____12663,arg_vars,elim_eqns_or_guards,uu____12666)
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
                                                                    let uu____12694
                                                                    =
                                                                    let uu____12701
                                                                    =
                                                                    let uu____12702
                                                                    =
                                                                    let uu____12713
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12724
                                                                    =
                                                                    let uu____12725
                                                                    =
                                                                    let uu____12730
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12730)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12725
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12713,
                                                                    uu____12724)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12702
                                                                     in
                                                                    (uu____12701,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12694
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let uu____12748
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12748
                                                                    then
                                                                    let x =
                                                                    let uu____12754
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12754,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12756
                                                                    =
                                                                    let uu____12763
                                                                    =
                                                                    let uu____12764
                                                                    =
                                                                    let uu____12775
                                                                    =
                                                                    let uu____12780
                                                                    =
                                                                    let uu____12783
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12783]
                                                                     in
                                                                    [uu____12780]
                                                                     in
                                                                    let uu____12788
                                                                    =
                                                                    let uu____12789
                                                                    =
                                                                    let uu____12794
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12795
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12794,
                                                                    uu____12795)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12789
                                                                     in
                                                                    (uu____12775,
                                                                    [x],
                                                                    uu____12788)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12764
                                                                     in
                                                                    let uu____12814
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12763,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12814)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12756
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12821
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
                                                                    (let uu____12849
                                                                    =
                                                                    let uu____12850
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____12850
                                                                    dapp1  in
                                                                    [uu____12849])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12821
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12857
                                                                    =
                                                                    let uu____12864
                                                                    =
                                                                    let uu____12865
                                                                    =
                                                                    let uu____12876
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12887
                                                                    =
                                                                    let uu____12888
                                                                    =
                                                                    let uu____12893
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12893)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12888
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12876,
                                                                    uu____12887)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12865
                                                                     in
                                                                    (uu____12864,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12857)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____12912 ->
                                                        ((let uu____12914 =
                                                            let uu____12919 =
                                                              let uu____12920
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____12921
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____12920
                                                                uu____12921
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____12919)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____12914);
                                                         ([], [])))
                                                in
                                             let uu____12926 = encode_elim ()
                                                in
                                             (match uu____12926 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____12946 =
                                                      let uu____12949 =
                                                        let uu____12952 =
                                                          let uu____12955 =
                                                            let uu____12958 =
                                                              let uu____12959
                                                                =
                                                                let uu____12970
                                                                  =
                                                                  let uu____12973
                                                                    =
                                                                    let uu____12974
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____12974
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12973
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____12970)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____12959
                                                               in
                                                            [uu____12958]  in
                                                          let uu____12979 =
                                                            let uu____12982 =
                                                              let uu____12985
                                                                =
                                                                let uu____12988
                                                                  =
                                                                  let uu____12991
                                                                    =
                                                                    let uu____12994
                                                                    =
                                                                    let uu____12997
                                                                    =
                                                                    let uu____12998
                                                                    =
                                                                    let uu____13005
                                                                    =
                                                                    let uu____13006
                                                                    =
                                                                    let uu____13017
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____13017)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13006
                                                                     in
                                                                    (uu____13005,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12998
                                                                     in
                                                                    let uu____13030
                                                                    =
                                                                    let uu____13033
                                                                    =
                                                                    let uu____13034
                                                                    =
                                                                    let uu____13041
                                                                    =
                                                                    let uu____13042
                                                                    =
                                                                    let uu____13053
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____13064
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____13053,
                                                                    uu____13064)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13042
                                                                     in
                                                                    (uu____13041,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13034
                                                                     in
                                                                    [uu____13033]
                                                                     in
                                                                    uu____12997
                                                                    ::
                                                                    uu____13030
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____12994
                                                                     in
                                                                  FStar_List.append
                                                                    uu____12991
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____12988
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____12985
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____12982
                                                             in
                                                          FStar_List.append
                                                            uu____12955
                                                            uu____12979
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____12952
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____12949
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____12946
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
           (fun uu____13110  ->
              fun se  ->
                match uu____13110 with
                | (g,env1) ->
                    let uu____13130 = encode_sigelt env1 se  in
                    (match uu____13130 with
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
      let encode_binding b uu____13195 =
        match uu____13195 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____13227 ->
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
                 ((let uu____13233 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13233
                   then
                     let uu____13234 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13235 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13236 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13234 uu____13235 uu____13236
                   else ());
                  (let uu____13238 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13238 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13254 =
                         let uu____13261 =
                           let uu____13262 =
                             let uu____13263 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13263
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13262  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13261
                          in
                       (match uu____13254 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13279 = FStar_Options.log_queries ()
                                 in
                              if uu____13279
                              then
                                let uu____13282 =
                                  let uu____13283 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13284 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13285 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13283 uu____13284 uu____13285
                                   in
                                FStar_Pervasives_Native.Some uu____13282
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____13301,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13315 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13315 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____13338,se,uu____13340) ->
                 let uu____13345 = encode_sigelt env1 se  in
                 (match uu____13345 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____13362,se) ->
                 let uu____13368 = encode_sigelt env1 se  in
                 (match uu____13368 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13385 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13385 with | (uu____13408,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13423 'Auu____13424 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13423,'Auu____13424)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13493  ->
              match uu____13493 with
              | (l,uu____13505,uu____13506) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13552  ->
              match uu____13552 with
              | (l,uu____13566,uu____13567) ->
                  let uu____13576 =
                    FStar_All.pipe_left
                      (fun _0_21  -> FStar_SMTEncoding_Term.Echo _0_21)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13577 =
                    let uu____13580 =
                      let uu____13581 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13581  in
                    [uu____13580]  in
                  uu____13576 :: uu____13577))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13608 =
      let uu____13611 =
        let uu____13612 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13615 =
          let uu____13616 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13616 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bindings = [];
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13612;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13615
        }  in
      [uu____13611]  in
    FStar_ST.op_Colon_Equals last_env uu____13608
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13654 = FStar_ST.op_Bang last_env  in
      match uu____13654 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13685 ->
          let uu___99_13688 = e  in
          let uu____13689 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bindings =
              (uu___99_13688.FStar_SMTEncoding_Env.bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___99_13688.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___99_13688.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___99_13688.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___99_13688.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___99_13688.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___99_13688.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13689
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13695 = FStar_ST.op_Bang last_env  in
    match uu____13695 with
    | [] -> failwith "Empty env stack"
    | uu____13725::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13760  ->
    let uu____13761 = FStar_ST.op_Bang last_env  in
    match uu____13761 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
        let top =
          let uu___100_13799 = hd1  in
          {
            FStar_SMTEncoding_Env.bindings =
              (uu___100_13799.FStar_SMTEncoding_Env.bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___100_13799.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___100_13799.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___100_13799.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = refs;
            FStar_SMTEncoding_Env.nolabels =
              (uu___100_13799.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___100_13799.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___100_13799.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___100_13799.FStar_SMTEncoding_Env.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13831  ->
    let uu____13832 = FStar_ST.op_Bang last_env  in
    match uu____13832 with
    | [] -> failwith "Popping an empty stack"
    | uu____13862::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> unit) =
  fun msg  ->
    push_env ();
    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.push ();
    FStar_SMTEncoding_Z3.push msg
  
let (pop : Prims.string -> unit) =
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
        | (uu____13944::uu____13945,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___101_13953 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___101_13953.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___101_13953.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___101_13953.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____13954 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____13973 =
        let uu____13976 =
          let uu____13977 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____13977  in
        let uu____13978 = open_fact_db_tags env  in uu____13976 ::
          uu____13978
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____13973
  
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
      let uu____14004 = encode_sigelt env se  in
      match uu____14004 with
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
        let uu____14046 = FStar_Options.log_queries ()  in
        if uu____14046
        then
          let uu____14049 =
            let uu____14050 =
              let uu____14051 =
                let uu____14052 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14052 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14051  in
            FStar_SMTEncoding_Term.Caption uu____14050  in
          uu____14049 :: decls
        else decls  in
      (let uu____14063 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14063
       then
         let uu____14064 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14064
       else ());
      (let env =
         let uu____14067 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14067 tcenv  in
       let uu____14068 = encode_top_level_facts env se  in
       match uu____14068 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14082 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14082)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____14098 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14098
       then
         let uu____14099 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14099
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14138  ->
                 fun se  ->
                   match uu____14138 with
                   | (g,env2) ->
                       let uu____14158 = encode_top_level_facts env2 se  in
                       (match uu____14158 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14181 =
         encode_signature
           (let uu___102_14190 = env  in
            {
              FStar_SMTEncoding_Env.bindings =
                (uu___102_14190.FStar_SMTEncoding_Env.bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___102_14190.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___102_14190.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___102_14190.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___102_14190.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___102_14190.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___102_14190.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___102_14190.FStar_SMTEncoding_Env.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14181 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14209 = FStar_Options.log_queries ()  in
             if uu____14209
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___103_14217 = env1  in
               {
                 FStar_SMTEncoding_Env.bindings =
                   (uu___103_14217.FStar_SMTEncoding_Env.bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___103_14217.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___103_14217.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___103_14217.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___103_14217.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___103_14217.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___103_14217.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___103_14217.FStar_SMTEncoding_Env.current_module_name)
               });
            (let uu____14219 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14219
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
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
        (let uu____14277 =
           let uu____14278 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14278.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14277);
        (let env =
           let uu____14280 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14280 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____14292 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____14329 = aux rest  in
                 (match uu____14329 with
                  | (out,rest1) ->
                      let t =
                        let uu____14359 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14359 with
                        | FStar_Pervasives_Native.Some uu____14364 ->
                            let uu____14365 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14365
                              x.FStar_Syntax_Syntax.sort
                        | uu____14366 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14370 =
                        let uu____14373 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___104_14376 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___104_14376.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___104_14376.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14373 :: out  in
                      (uu____14370, rest1))
             | uu____14381 -> ([], bindings1)  in
           let uu____14388 = aux bindings  in
           match uu____14388 with
           | (closing,bindings1) ->
               let uu____14413 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14413, bindings1)
            in
         match uu____14292 with
         | (q1,bindings1) ->
             let uu____14436 =
               let uu____14441 =
                 FStar_List.filter
                   (fun uu___86_14446  ->
                      match uu___86_14446 with
                      | FStar_TypeChecker_Env.Binding_sig uu____14447 ->
                          false
                      | uu____14454 -> true) bindings1
                  in
               encode_env_bindings env uu____14441  in
             (match uu____14436 with
              | (env_decls,env1) ->
                  ((let uu____14472 =
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
                    if uu____14472
                    then
                      let uu____14473 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14473
                    else ());
                   (let uu____14475 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14475 with
                    | (phi,qdecls) ->
                        let uu____14496 =
                          let uu____14501 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14501 phi
                           in
                        (match uu____14496 with
                         | (labels,phi1) ->
                             let uu____14518 = encode_labels labels  in
                             (match uu____14518 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14555 =
                                      let uu____14562 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14563 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14562,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14563)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14555
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
  